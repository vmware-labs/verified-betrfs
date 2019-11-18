using System;
using System.Diagnostics;
using System.Collections.Generic;

abstract class Benchmark {
  public abstract string Name { get; }

  public void Run() {
    FSUtil.ClearIfExists();
    FSUtil.Mkfs();
    Application app = new Application();
    app.verbose = false;

    Prepare(app);

    GC.Collect();

    Stopwatch sw = Stopwatch.StartNew();
    Go(app);
    int opCount = OpCount(app);
    sw.Stop();

    Console.WriteLine("Benchmark " + Name + ": " + (((double) opCount) / (((double) sw.ElapsedMilliseconds) / 1000)).ToString() + " ops/s" + ", " + sw.ElapsedMilliseconds.ToString() + " ms" + ", " + opCount.ToString() + " ops");
  }

  abstract protected void Prepare(Application app);
  abstract protected void Go(Application app);

  abstract protected int OpCount(Application app);

  protected List<byte[]> RandomSeqs(int n, int seed, int len) {
    Random rand = new Random(seed);

    List<byte[]> l = new List<byte[]>();
    for (int i = 0; i < n; i++) {
      byte[] bytes = new byte[len];
      rand.NextBytes(bytes);
      l.Add(bytes);
    }

    return l;
  }

  protected List<byte[]> RandomKeys(int n, int seed) {
    return RandomSeqs(n, seed, 20);
  }

  protected List<byte[]> RandomValues(int n, int seed) {
    return RandomSeqs(n, seed, 400);
  }

  protected List<byte[]> RandomSortedKeys(int n, int seed) {
    List<byte[]> data = RandomKeys(n, seed);
    data.Sort(new ArrayComparer());
    return data;
  }

  class ArrayComparer : IComparer<byte[]>
  {
    // Call CaseInsensitiveComparer.Compare with the parameters reversed.
    public int Compare(byte[] x, byte[] y)
    {
      byte[] a = (byte[]) x;
      byte[] b = (byte[]) y;
      for (int i = 0; i < a.Length && i < b.Length; i++) {
        if (a[i] < b[i]) return -1;
        if (a[i] > b[i]) return 1;
      }
      if (a.Length < b.Length) return -1;
      if (a.Length > b.Length) return 1;
      return 0;
    }
  }

  // Generate random keys to query.
  // Half will be existing keys, half will be totally random keys
  protected void RandomQueryKeysAndValues(int n, int seed, List<byte[]> insertedKeys, List<byte[]> insertedValues,
      out List<byte[]> queryKeys, out List<byte[]> queryValues) {
    Random rand = new Random(seed);

    byte[] emptyBytes = new byte[0];

    queryKeys = new List<byte[]>();
    queryValues = new List<byte[]>();
    for (int i = 0; i < n; i++) {
      if (rand.Next(0, 2) == 0) {
        // Min length 20 so probability of collision is miniscule
        byte[] bytes = new byte[20];
        rand.NextBytes(bytes);
        queryKeys.Add(bytes);
        queryValues.Add(emptyBytes);
      } else {
        int idx = rand.Next(0, insertedKeys.Count);
        queryKeys.Add(insertedKeys[idx]);
        queryValues.Add(insertedValues[idx]);
      }
    }
  }
}

class BenchmarkRandomInserts : Benchmark {
  public override string Name { get { return "RandomInserts"; } }

  List<byte[]> keys;
  List<byte[]> values;

  int count = 500000;

  public BenchmarkRandomInserts() {
    int seed1 = 1234;
    int seed2 = 527;
    keys = RandomKeys(count, seed1);
    values = RandomValues(count, seed2);
  }

  override protected void Prepare(Application app) {
  }

  override protected int OpCount(Application app) {
    return count;
  }

  override protected void Go(Application app) {
    for (int i = 0; i < keys.Count; i++) {
      app.Insert(keys[i], values[i]);
    }
    Console.Error.Write("? sync ");
    //Native_Compile.BenchmarkingUtil.start();
    app.Sync();
    //Native_Compile.BenchmarkingUtil.end();
    Console.Error.WriteLine("done");
  }
}

// 50_000_000 random inserts
//
// This harness can generate ~2_300_000 ops/s on my machine (only generating keys and values, not calling Insert/Sync)
class LongBenchmarkRandomInserts : Benchmark {
  public override string Name { get { return "LongRandomInserts"; } }

  int count = 5_000_000;

  override protected int OpCount(Application app) {
    return count;
  }

  public LongBenchmarkRandomInserts() {
  }

  override protected void Prepare(Application app) {
  }

  uint rngState = 198432;

  protected uint NextPseudoRandom() {
    rngState = (uint) (((ulong) rngState * 279470273) % 0xfffffffb);
    return rngState;
  }

  unsafe override protected void Go(Application app) {

    for (uint i = 0; i < this.count; i++) {
      byte[] keyBytes = new byte[20];
      for (uint j = 0; j < 20; j += 4) {
        fixed (byte* ptr = &keyBytes[j]) {
          uint* intPtr = (uint*) ptr;
          *intPtr = NextPseudoRandom();
        }
      }
      byte[] valueBytes = new byte[400];
      for (uint j = 0; j < 400; j += 4) {
        fixed (byte* ptr = &valueBytes[j]) {
          uint* intPtr = (uint*) ptr;
          *intPtr = NextPseudoRandom();
        }
      }
      // Console.Error.WriteLine("KEY " + BitConverter.ToString(keyBytes));
      app.Insert(keyBytes, valueBytes);
      if (i % 1000000 == 0 && i != 0) {
        Console.Error.WriteLine("? at " + i.ToString() + " ");
        //app.Sync();
        //Console.Error.WriteLine("done");
      }
    }
    Console.Error.WriteLine("? sync at " + this.count + " ");
    app.Sync();
    Console.WriteLine("done");
  }
}

class BenchmarkRandomQueries : Benchmark {
  public override string Name { get { return "RandomQueries"; } }

  List<byte[]> keys;
  List<byte[]> values;
  List<byte[]> query_keys;
  List<byte[]> query_values;

  int count = 500000;

  public BenchmarkRandomQueries() {
    int seed1 = 1234;
    int seed2 = 527;
    int seed3 = 19232;
    keys = RandomKeys(count, seed1);
    values = RandomValues(count, seed2);
    RandomQueryKeysAndValues(count, seed3, keys, values, out query_keys, out query_values);
  }

  override protected void Prepare(Application app) {
    for (int i = 0; i < keys.Count; i++) {
      app.Insert(keys[i], values[i]);
    }
    app.Sync();
    app.crash();
  }

  override protected int OpCount(Application app) {
    return count;
  }

  override protected void Go(Application app) {
    for (int i = 0; i < query_keys.Count; i++) {
      app.QueryAndExpect(query_keys[i], query_values[i]);
    }
  }
}

class BenchmarkSequentialInserts : Benchmark {
  public override string Name { get { return "SeqentialInserts"; } }

  List<byte[]> keys;
  List<byte[]> values;

  int count = 500000;

  public BenchmarkSequentialInserts() {
    int seed1 = 1234;
    int seed2 = 527;
    keys = RandomSortedKeys(count, seed1);
    values = RandomValues(count, seed2);
  }

  override protected void Prepare(Application app) {
  }

  override protected int OpCount(Application app) {
    return count;
  }

  override protected void Go(Application app) {
    for (int i = 0; i < keys.Count; i++) {
      app.Insert(keys[i], values[i]);
    }
    app.Sync();
  }
}

class BenchmarkSequentialQueries : Benchmark {
  public override string Name { get { return "SequentialQueries"; } }

  List<byte[]> keys;
  List<byte[]> values;

  int count = 500000;

  public BenchmarkSequentialQueries() {
    int seed1 = 1234;
    int seed2 = 527;
    keys = RandomSortedKeys(count, seed1);
    values = RandomValues(count, seed2);
  }

  override protected void Prepare(Application app) {
    for (int i = 0; i < keys.Count; i++) {
      app.Insert(keys[i], values[i]);
    }
    app.Sync();
    app.crash();
  }

  override protected int OpCount(Application app) {
    return count;
  }

  override protected void Go(Application app) {
    for (int i = 0; i < keys.Count; i++) {
      app.QueryAndExpect(keys[i], values[i]);
    }
  }
}

class Hashing : Benchmark {
  public override string Name { get { return "Hashing"; } }

  const int size = 1024*1024;

  byte[] b;
  //byte[] a;
  
  int count = 10;

  public Hashing() {
  }

  override protected void Prepare(Application app) {
    b = new byte[size];
  }

  override protected int OpCount(Application app) {
    return count;
  }

  override protected void Go(Application app) {
    for (int i = 0; i < count; i++) {
      Crypto_Compile.__default.Crc32C(new Dafny.Sequence<byte>(b));
      /*a = new byte[size];
      for (int j = 0; j < size; j++) {
        a[j] = b[j];
      }*/
    }
  }
}

class Benchmarks {
  public void RunAllBenchmarks() {
    new BenchmarkRandomQueries().Run();
    new BenchmarkRandomInserts().Run();
    new BenchmarkSequentialQueries().Run();
    new BenchmarkSequentialInserts().Run();
    // new Hashing().Run();

    NativeBenchmarking_Compile.__default.dump();
  }

  static Dictionary<string, Func<Benchmark>> _benchmarks = new Dictionary<string, Func<Benchmark>>
  {
    { "random-queries", () => new BenchmarkRandomQueries() }, 
    { "random-inserts", () => new BenchmarkRandomInserts() }, 
    { "sequential-queries", () => new BenchmarkSequentialQueries() }, 
    { "sequential-inserts", () => new BenchmarkSequentialInserts() }, 
    { "long-random-inserts", () => new LongBenchmarkRandomInserts() }, 
  };

  public void RunBenchmark(String name) {
    if (!_benchmarks.ContainsKey(name)) {
        Console.WriteLine("invalid benchmark, either use --all-benchmarks or choose one of the following with --benchmark=name:");
        foreach (var k in _benchmarks.Keys) {
            Console.WriteLine("    " + k);
        }
    }
    (_benchmarks[name])().Run();

    NativeBenchmarking_Compile.__default.dump();
  }
}

namespace NativeBenchmarking_Compile {
  public class StopwatchEntry {
    public Stopwatch s;
    public int count;
    public StopwatchEntry() {
      s = new Stopwatch();
      count = 0;
    }
  }

  public partial class __default
  {
    public static Dictionary<string, StopwatchEntry> sw = new Dictionary<string, StopwatchEntry>();

    public static string nameToString(Dafny.Sequence<char> dafnyName) {
      ArraySegment<char> seg = (ArraySegment<char>) dafnyName.Elements;
      return new string(seg.Array, seg.Offset, seg.Count);
    }

    public static void start(Dafny.Sequence<char> dafnyName) {
      start(nameToString(dafnyName));
    }

    public static void end(Dafny.Sequence<char> dafnyName) {
      end(nameToString(dafnyName));
    }

    public static void start(string name) {
      if (!sw.ContainsKey(name)) {
        sw.Add(name, new StopwatchEntry());
      }
      StopwatchEntry p = sw[name];
      p.s.Start();
      p.count++;
    }
    public static void end(string name) {
      StopwatchEntry p = sw[name];
      p.s.Stop();
    }
    public static void dump() {
      foreach (var k in sw) {
        string name = k.Key;
        int count = k.Value.count;
        Stopwatch s = k.Value.s;
        Console.WriteLine(name + " " + s.ElapsedMilliseconds.ToString() + " ms, " + count + " ticks");
      }
    }
  }
}
