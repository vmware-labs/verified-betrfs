#include "Application.h"
#include "Benchmarks.h"

using namespace std;

int main(int argc, char* argv[]) {
  bool allBenchmarks = false;
  string benchmark;

  for (int i = 1; i < argc; i++) {
    string arg = string(argv[i]);

    if (arg == "--all-benchmarks") {
      allBenchmarks = true;
    } else if (arg.substr(0, 12) == "--benchmark=") {
      benchmark = arg.substr(12);
    }
  }

  if (allBenchmarks) {
    RunAllBenchmarks();
  } else if (benchmark != "") {
    RunBenchmark(benchmark);
  } else {
    cout << "Use --all-benchmarks or --benchmark" << endl;
  }
}

/*int main()
{
  Mkfs();
  cout << "Mkfs done" << endl;

  Application app;
  app.Insert("abc", "def");
  app.Insert("xyq", "rawr");
  app.Query("abc");

  app.Query("xyq");
  app.Query("blahblah");
  app.crash();
  app.Query("abc");
  app.Query("xyq");

  app.Insert("abc", "def");
  app.Insert("xyq", "rawr");
  app.Insert("blahblah", "moomoo");
  app.Sync();
  app.crash();
  app.Query("abc");
  app.Query("xyq");
}*/
