#include "Application.h"
#include "Benchmarks.h"

using namespace std;

int main(int argc, char* argv[]) {
  bool allBenchmarks = false;
  string benchmark;
  bool skipPrepare = false;
  string image = ".veribetrfs.img";
  
  for (int i = 1; i < argc; i++) {
    string arg = string(argv[i]);

    if (arg == "--all-benchmarks") {
      allBenchmarks = true;
    } else if (arg.substr(0, 12) == "--benchmark=") {
      benchmark = arg.substr(12);
    } else if (arg == "--skip-prepare") {
      skipPrepare = true;
    } else if (arg[0] != '-') {
      image = arg;
    } else {
      cout << "Unrecognized argument: " << arg << endl;
      return 1;
    }
  }

  if (allBenchmarks) {
    RunAllBenchmarks(image);
  } else if (benchmark != "") {
    RunBenchmark(image, benchmark, skipPrepare);
  } else {
    cout << "Usage: Veribetrfs --all-benchmarks [disk.img]" << endl;
    cout << "Usage: Veribetrfs [--skip-prepare] --benchmark=<benchmark> [disk.img]" << endl;
    cout << "Default disk image is .veribetrfs.img" << endl;
  }
}

/*void test_succ(Application& app, string s, bool inclusive, int num) {
  auto res = app.Succ(ByteString(s), inclusive, num);
  cout << "Succ for " << s << " " << (inclusive ? "inclusive" : "exclusive") << " for " << num << endl;
  for (auto p : res) {
    cout << "    " << p.first.as_string() << " : " << p.second.as_string() << endl;
  }
}*/

/*int main()
{
  ClearIfExists();
  Mkfs();
  cout << "Mkfs done" << endl;

  Application app;
  cout << "Inserting..." << endl;
  app.Insert("abc", "def");
  cout << "done first insert..." << endl;
  app.Insert("xyq", "rawr");
  app.Query("abc");

  app.Query("xyq");
  app.Query("blahblah");
  app.crash();
  cout << "crashed" << endl;
  app.Query("abc");
  app.Query("xyq");

  app.Insert("abc", "def");
  app.Insert("xyq", "rawr");
  app.Insert("blahblah", "moomoo");
  app.Sync();
  app.crash();

  app.Query("abc");
  app.Query("xyq");

  test_succ(app, "abc", true, 1);
  test_succ(app, "abc", true, 2);
  test_succ(app, "abc", true, 3);
  test_succ(app, "abc", true, 4);
  test_succ(app, "abc", true, 5);
  test_succ(app, "abc", false, 5);

  test_succ(app, "blahblah", true, 5);
  test_succ(app, "blahblah", false, 5);

  test_succ(app, "car", true, 5);
  test_succ(app, "car", false, 5);

  test_succ(app, "xyq", true, 5);
  test_succ(app, "xyq", false, 5);

  test_succ(app, "zaz", true, 5);
  test_succ(app, "zaz", false, 5);
}*/
