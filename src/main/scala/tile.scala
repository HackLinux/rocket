// See LICENSE for license details.

package rocket

import Chisel._
import uncore._
import Util._

case object CoreName extends Field[String]
case object NDCachePorts extends Field[Int]
case object NTilePorts extends Field[Int]
case object NPTWPorts extends Field[Int]
case object BuildRoCC extends Field[Option[() => RoCC]]

abstract class Tile(resetSignal: Bool = null) extends Module(_reset = resetSignal) {
  val io = new Bundle {
    val tilelink = new TileLinkIO
    val host = new HTIFIO
  }
}

class RocketTile(resetSignal: Bool = null) extends Tile(resetSignal) {

  val icache = Module(new Frontend, { case CacheName => "L1I"; case CoreName => "Rocket" })
  val dcache = Module(new HellaCache, { case CacheName => "L1D" })
  val ptw = Module(new PTW(params(NPTWPorts)))
  val core = Module(new Core, { case CoreName => "Rocket" })

  val dcArb = Module(new HellaCacheArbiter(params(NDCachePorts)))
  dcArb.io.requestor(0) <> ptw.io.mem
  dcArb.io.requestor(1) <> core.io.dmem
  dcArb.io.mem <> dcache.io.cpu

  ptw.io.requestor(0) <> icache.io.cpu.ptw
  ptw.io.requestor(1) <> dcache.io.cpu.ptw

  core.io.host <> io.host
  core.io.imem <> icache.io.cpu
  core.io.ptw <> ptw.io.dpath

  val memArb = Module(new TileLinkIOArbiterThatAppendsArbiterId(params(NTilePorts)))
  io.tilelink <> memArb.io.out
  memArb.io.in(0) <> dcache.io.mem
  memArb.io.in(1) <> TileLinkIOWrapper(icache.io.mem)

  //If so specified, build an RoCC module and wire it in
  params(BuildRoCC)
    .map { br => br() }
    .foreach { rocc =>
      val dcIF = Module(new SimpleHellaCacheIF)
      core.io.rocc <> rocc.io
      dcIF.io.requestor <> rocc.io.mem
      dcArb.io.requestor(2) <> dcIF.io.cache
      memArb.io.in(2) <> TileLinkIOWrapper(rocc.io.imem)
      memArb.io.in(3) <> rocc.io.dmem
      ptw.io.requestor(2) <> rocc.io.iptw
      ptw.io.requestor(3) <> rocc.io.dptw
      ptw.io.requestor(4) <> rocc.io.pptw
    }
}
