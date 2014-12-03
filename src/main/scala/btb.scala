// See LICENSE for license details.

package rocket

import Chisel._
import Util._
import Node._
import uncore._

case object NBTBEntries extends Field[Int]
case object NRAS extends Field[Int]

abstract trait BTBParameters extends UsesParameters {
  val vaddrBits = params(VAddrBits)
  val matchBits = params(PgIdxBits)
  val entries = params(NBTBEntries)
  val nRAS = params(NRAS)
  // why nPages ~ log2Up(entries)?
  // since the branch prediction works good in a single thread (small memroy space, one page perhaps)
  // the entries should share the same but smaller set of pages
  // using another index table to store pages rather than one page per entry
  // to save space?
  val nPages = ((1 max(log2Up(entries)))+1)/2*2 // control logic assumes 2 divides pages
  val opaqueBits = log2Up(entries)
  val nBHT = 1 << log2Up(entries*2)
}

// return address stack
class RAS(nras: Int) {
  def push(addr: UInt): Unit = {
    when (count < nras) { count := count + 1 }
    val nextPos = Mux(Bool(isPow2(nras)) || pos > 0, pos+1, UInt(0)) // the guard seems unneccessary
    stack(nextPos) := addr
    pos := nextPos
  }
  def peek: UInt = stack(pos)
  def pop: Unit = when (!isEmpty) {
    count := count - 1
    pos := Mux(Bool(isPow2(nras)) || pos > 0, pos-1, UInt(nras-1))  // the guard seems unneccessary
  }
  def clear: Unit = count := UInt(0)
  def isEmpty: Bool = count === UInt(0)

  private val count = Reg(init=UInt(0,log2Up(nras+1)))
  private val pos = Reg(init=UInt(0,log2Up(nras)))
  private val stack = Vec.fill(nras){Reg(UInt())}
}

class BHTResp extends Bundle with BTBParameters {
  val history = UInt(width = log2Up(nBHT).max(1))
  val value = UInt(width = 2)
}

// Brach history table
// Gshare branch predictor
//   Reference:  Scott McFarling. Combining branch predictors. WRL Technical Note TN-36, Western Research Laboratory, 1993
//               Section 7. Global history with index sharing
//                          Figure 10
// Using a global branch history and one table to predict branch results.
// The multiple local tables are shared into one table using the addr ^ hist hash method
class BHT(nbht: Int) {
  val nbhtbits = log2Up(nbht)
  def get(addr: UInt, update: Bool): BHTResp = {
    val res = new BHTResp
    val index = addr(nbhtbits+1,2) ^ history
    res.value := table(index)
    res.history := history
    val taken = res.value(0)
    when (update) { history := Cat(taken, history(nbhtbits-1,1)) }
    res
  }
  def update(addr: UInt, d: BHTResp, taken: Bool, mispredict: Bool): Unit = {
    val index = addr(nbhtbits+1,2) ^ d.history
    table(index) := Cat(taken, (d.value(1) & d.value(0)) | ((d.value(1) | d.value(0)) & taken))
    when (mispredict) { history := Cat(taken, d.history(nbhtbits-1,1)) }
  }

  private val table = Mem(UInt(width = 2), nbht) // 2-bit history
  val history = Reg(UInt(width = nbhtbits))
}

class BTBUpdate extends Bundle with BTBParameters {
  val prediction = Valid(new BTBResp)         // the actual branch result from the core 
  val pc = UInt(width = vaddrBits)            // the pc of the branch instruction
  val target = UInt(width = vaddrBits)        // the actual target (next pc)
  val returnAddr = UInt(width = vaddrBits)    // the return address when JALR (function jump with return)
  val taken = Bool()
  val isJump = Bool()
  val isCall = Bool()
  val isReturn = Bool()
  val mispredict = Bool()
}

class BTBResp extends Bundle with BTBParameters {
  val taken = Bool()                          // the  predicted taken from BHT
  val target = UInt(width = vaddrBits)        // the predicted branch target from BTB 
  val entry = UInt(width = opaqueBits)        // entry index in the BTB 
  val bht = new BHTResp                       // follow the instruction until when updated (incl history and entry)
}

class BTBReq extends Bundle with BTBParameters {
   val addr = UInt(width = vaddrBits)
}

// fully-associative branch target buffer
class BTB extends Module with BTBParameters {
  val io = new Bundle {
    val req = Valid(new BTBReq).flip         // request from icache
    val resp = Valid(new BTBResp)            // branch prediction to icache and core
    val update = Valid(new BTBUpdate).flip   // branch update from core
    val invalidate = Bool(INPUT)
  }

  // for each entry
  // [          idx       ][       tgt        ]
  //   pc[matchBits-1:0]       branch target


  val idxValid = Reg(init=UInt(0, entries))                 // whether the entry is valid 
  val idxs = Mem(UInt(width=matchBits), entries)            // the array of source pc
  val idxPages = Mem(UInt(width=log2Up(nPages)), entries)   // page pointer
  val tgts = Mem(UInt(width=matchBits), entries)            // the array of branch target
  val tgtPages = Mem(UInt(width=log2Up(nPages)), entries)   // page pointer
  val pages = Mem(UInt(width=vaddrBits-matchBits), nPages)  // page field
  val pageValid = Reg(init=UInt(0, nPages))                 // whether a page is valid
  val idxPagesOH = idxPages.map(UIntToOH(_)(nPages-1,0))    // one-hot of idxPages
  val tgtPagesOH = tgtPages.map(UIntToOH(_)(nPages-1,0))    // one-hot of tgtPages

  val useRAS = Reg(UInt(width = entries))                   // specify certain entries for return 
  val isJump = Reg(UInt(width = entries))                   // specify certain entries for jump

  private def page(addr: UInt) = addr >> matchBits          // get the page field of an addr 
  private def pageMatch(addr: UInt) = {                     // check if there is a page matching with this addr
    val p = page(addr)
    Vec(pages.map(_ === p)).toBits & pageValid
  }
  private def tagMatch(addr: UInt, pgMatch: UInt): UInt = { // whether addr matches an idx and pgMatch matches a page
    val idx = addr(matchBits-1,0)
    val idxMatch = idxs.map(_ === idx).toBits
    val idxPageMatch = idxPagesOH.map(_ & pgMatch).map(_.orR).toBits
    idxValid & idxMatch & idxPageMatch
  }

  val r_update = Pipe(io.update)                             // delay io.update for 1 cycle 
  val update_target = io.req.bits.addr                       // the new branch target if valid

  val pageHit = pageMatch(io.req.bits.addr)                  // prediction request matches with pages in the BTB
  val hits = tagMatch(io.req.bits.addr, pageHit)             // find a possible hit for request
  val updatePageHit = pageMatch(r_update.bits.pc)            // update matches with pages in the BTB
  val updateHits = tagMatch(r_update.bits.pc, updatePageHit) // find a possible hit for update

  private var lfsr = LFSR16(r_update.valid)
  def rand(width: Int) = {
    lfsr = lfsr(lfsr.getWidth-1,1)
    Random.oneHot(width, lfsr)
  }

  val updateHit = r_update.bits.prediction.valid                                     // BTB needs update due to branch 
  val updateValid = r_update.bits.mispredict || updateHit && Bool(nBHT > 0)          // indeed need an update when hit (with BHT) or mispredict 
  val updateTarget = updateValid && r_update.bits.mispredict && r_update.bits.taken  // need to update the predicted target 

  val useUpdatePageHit = updatePageHit.orR                                           // page hit for update 
  val doIdxPageRepl = updateTarget && !useUpdatePageHit                              // need to replace a page (need update but no page hit) 
  val idxPageRepl = UInt()                                                           // the page to be replaced due to no hit for update 
  val idxPageUpdateOH = Mux(useUpdatePageHit, updatePageHit, idxPageRepl)             
  val idxPageUpdate = OHToUInt(idxPageUpdateOH)                                      // get the page to be updated (hit or replace) 
  val idxPageReplEn = Mux(doIdxPageRepl, idxPageRepl, UInt(0))                       // enable replacing a page 

  // a single misprediction may require two page entries to be written
  // one for the miss branch source (due to invalidate or initial empty buffer)
  // the other due to the branch target

  val samePage = page(r_update.bits.pc) === page(update_target)                      // branch source and target in the same page 
  val usePageHit = (pageHit & ~idxPageReplEn).orR 
  val doTgtPageRepl = updateTarget && !samePage && !usePageHit
  val tgtPageRepl = Mux(samePage, idxPageUpdateOH, idxPageUpdateOH(nPages-2,0) << 1 | idxPageUpdateOH(nPages-1)) // if not the same page, use the previous one to avoid being replaced immediately afterwords. (FIFO replacement)
  val tgtPageUpdate = OHToUInt(Mux(usePageHit, pageHit, tgtPageRepl))
  val tgtPageReplEn = Mux(doTgtPageRepl, tgtPageRepl, UInt(0))
  val doPageRepl = doIdxPageRepl || doTgtPageRepl

  val pageReplEn = idxPageReplEn | tgtPageReplEn
  idxPageRepl := UIntToOH(Counter(r_update.valid && doPageRepl, nPages)._1)           // increase every time a new page is needed, FIFO replace? 

  when (r_update.valid && !(updateValid && !updateTarget)) {
    val nextRepl = Counter(!updateHit && updateValid, entries)._1                     // increase every time a new entry is needed, FIFO replace? 
    val waddr = Mux(updateHit, r_update.bits.prediction.bits.entry, nextRepl)

    // invalidate entries if we stomp on pages they depend upon
    idxValid := idxValid & ~Vec.tabulate(entries)(i => (pageReplEn & (idxPagesOH(i) | tgtPagesOH(i))).orR).toBits

    idxValid(waddr) := updateValid
    when (updateTarget) {
      assert(io.req.bits.addr === r_update.bits.target, "BTB request != I$ target")
      idxs(waddr) := r_update.bits.pc
      tgts(waddr) := update_target
      idxPages(waddr) := idxPageUpdate
      tgtPages(waddr) := tgtPageUpdate
      useRAS(waddr) := r_update.bits.isReturn
      isJump(waddr) := r_update.bits.isJump
    }

    require(nPages % 2 == 0)
    val idxWritesEven = (idxPageUpdateOH & Fill(nPages/2, UInt(1,2))).orR

    def writeBank(i: Int, mod: Int, en: Bool, data: UInt) =
      for (i <- i until nPages by mod)
        when (en && pageReplEn(i)) { pages(i) := data }

    // divide the page entries into 2 banks
    // since the maximally 2 entries to be written are located in different banks
    // they can be processed in parallel
    writeBank(0, 2, Mux(idxWritesEven, doIdxPageRepl, doTgtPageRepl),
      Mux(idxWritesEven, page(r_update.bits.pc), page(update_target)))
    writeBank(1, 2, Mux(idxWritesEven, doTgtPageRepl, doIdxPageRepl),
      Mux(idxWritesEven, page(update_target), page(r_update.bits.pc)))

    when (doPageRepl) { pageValid := pageValid | pageReplEn }
  }

  // invalidate the whole BTB?
  when (io.invalidate) {
    idxValid := 0  
    pageValid := 0
  }

  io.resp.valid := hits.orR
  io.resp.bits.taken := io.resp.valid
  io.resp.bits.target := Cat(Mux1H(Mux1H(hits, tgtPagesOH), pages), Mux1H(hits, tgts))
  io.resp.bits.entry := OHToUInt(hits)

  // Brach history table
  if (nBHT > 0) {
    val bht = new BHT(nBHT)
    val res = bht.get(io.req.bits.addr, io.req.valid && hits.orR && !Mux1H(hits, isJump)) // no update for Jump which is fixed
    val update_btb_hit = io.update.bits.prediction.valid
    when (io.update.valid && update_btb_hit && !io.update.bits.isJump) {
      bht.update(io.update.bits.pc, io.update.bits.prediction.bits.bht,
                 io.update.bits.taken, io.update.bits.mispredict)
    }
    when (!res.value(0) && !Mux1H(hits, isJump)) { io.resp.bits.taken := false }
    io.resp.bits.bht := res
  }

  // return address stack
  if (nRAS > 0) {
    val ras = new RAS(nRAS)
    val doPeek = Mux1H(hits, useRAS)
    when (!ras.isEmpty && doPeek) {
      io.resp.bits.target := ras.peek
    }
    when (io.update.valid) {
      when (io.update.bits.isCall) {
        ras.push(io.update.bits.returnAddr)
        when (doPeek) {
          io.resp.bits.target := io.update.bits.returnAddr // not very sure why this is needed
        }
      }.elsewhen (io.update.bits.isReturn && io.update.bits.prediction.valid) {
        ras.pop
      }
    }
    when (io.invalidate) { ras.clear }
  }
}
