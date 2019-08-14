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

    Console.WriteLine("Benchmark " + Name + ": " + (opCount / (sw.ElapsedMilliseconds / 1000)).ToString() + " ops/s" + ", " + sw.ElapsedMilliseconds.ToString() + " ms" + ", " + opCount.ToString() + " ops");
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
    app.Sync();
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
      Crypto_Compile.__default.Crc32(new Dafny.Sequence<byte>(b));
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
    //new Hashing().Run();

    Native_Compile.BenchmarkingUtil.dump();
  }
}

namespace Native_Compile {
  public partial class BenchmarkingUtil
  {
    public static Stopwatch sw = null;
    public static int count = 0;
    public static void start() {
      if (sw == null) {
        sw = new Stopwatch();
      }
      sw.Start();
      count++;
    }
    public static void end() {
      sw.Stop();
    }
    public static void dump() {
      if (sw != null) {
        Console.WriteLine("measured time: " + sw.ElapsedMilliseconds.ToString());
        Console.WriteLine("calls: " + count.ToString());
      }
    }
  }
}
