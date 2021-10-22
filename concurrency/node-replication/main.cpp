#include "DafnyRuntime.h"

// Include Extern.h before generated Bundle.i.h.
// Bundle.i.h depends on it but it can't include it itself.
#include "Extern.h"
#include "LinearExtern.h"
#include "Bundle.i.h"

int main(int argc, char* argv[]) {
  auto nr = Init_ON_CounterIfc__Compile::__default::initNR();

  return 0;
}
