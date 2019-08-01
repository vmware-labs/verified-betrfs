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
    sw.Stop();

    Console.WriteLine("Benchmark " + Name + " " + sw.ElapsedMilliseconds.ToString() + " ms");
  }

  abstract protected void Prepare(Application app);
  abstract protected void Go(Application app);

  protected List<byte[]> RandomKeys(int n, int seed) {
    Random rand = new Random(seed);

    List<byte[]> l = new List<byte[]>();
    for (int i = 0; i < n; i++) {
      int sz = rand.Next(1, 1024 + 1);
      byte[] bytes = new byte[sz];
      rand.NextBytes(bytes);
      l.Add(bytes);
    }

    return l;
  }

  protected List<byte[]> RandomValues(int n, int seed) {
    return RandomKeys(n, seed);
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
        int sz = rand.Next(20, 1024 + 1);
        byte[] bytes = new byte[sz];
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

  public BenchmarkRandomInserts() {
    int seed1 = 1234;
    int seed2 = 527;
    keys = RandomKeys(20000, seed1);
    values = RandomValues(20000, seed2);
  }

  override protected void Prepare(Application app) {
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

  public BenchmarkRandomQueries() {
    int seed1 = 1234;
    int seed2 = 527;
    int seed3 = 19232;
    keys = RandomKeys(20000, seed1);
    values = RandomValues(20000, seed2);
    RandomQueryKeysAndValues(20000, seed3, keys, values, out query_keys, out query_values);
  }

  override protected void Prepare(Application app) {
    for (int i = 0; i < keys.Count; i++) {
      app.Insert(keys[i], values[i]);
    }
    app.Sync();
    app.crash();
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

  public BenchmarkSequentialInserts() {
    int seed1 = 1234;
    int seed2 = 527;
    keys = RandomSortedKeys(20000, seed1);
    values = RandomValues(20000, seed2);
  }

  override protected void Prepare(Application app) {
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

  public BenchmarkSequentialQueries() {
    int seed1 = 1234;
    int seed2 = 527;
    keys = RandomSortedKeys(20000, seed1);
    values = RandomValues(20000, seed2);
  }

  override protected void Prepare(Application app) {
    for (int i = 0; i < keys.Count; i++) {
      app.Insert(keys[i], values[i]);
    }
    app.Sync();
    app.crash();
  }

  override protected void Go(Application app) {
    for (int i = 0; i < keys.Count; i++) {
      app.QueryAndExpect(keys[i], values[i]);
    }
  }
}

class Benchmarks {
  public void RunAllBenchmarks() {
    //new BenchmarkRandomQueries().Run();
    new BenchmarkRandomInserts().Run();
    //new BenchmarkSequentialQueries().Run();
    //new BenchmarkSequentialInserts().Run();
  }
}
