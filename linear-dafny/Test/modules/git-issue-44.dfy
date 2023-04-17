// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cpp "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module Ifc { }

abstract module InputOutputIfc refines Ifc { }

abstract module DiskSSM(IOIfc: InputOutputIfc) { }

module DiskSSMTokens(ioifc: InputOutputIfc, ssm: DiskSSM(ioifc)) {
  type Token = int
}

abstract module AIOParams { }

module AIO(aioparams: AIOParams, ioifc: InputOutputIfc, ssm: DiskSSM(ioifc)) {
  import T = DiskSSMTokens(ioifc, ssm)
}

method Main()
{
}
