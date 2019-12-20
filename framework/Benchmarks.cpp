#include "Benchmarks.h"

#include <chrono>
#include <iostream>
#include <random>

#include "Application.h"

using namespace std;

class Benchmark {
public:
  virtual ~Benchmark() {}

  virtual string name() = 0;
  virtual int opCount() = 0;
  virtual void prepare(Application& app) = 0;
  virtual void go(Application& app) = 0;

  void run() {
    ClearIfExists();
    Mkfs();

    Application app;

    prepare(app);

    auto t1 = chrono::high_resolution_clock::now();
    go(app);
    auto t2 = chrono::high_resolution_clock::now();

    long long ms = std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();

    cout << "Benchmark " << name() << ": "
         << (((double) opCount()) / (((double) ms) / 1000)) << " ops/s, "
         << ms << " ms, "
         << opCount() << " ops"
				 << endl;
  }

  vector<ByteString> RandomSeqs(int n, int seed, int len) {
    std::default_random_engine gen;
    gen.seed(seed);
    std::uniform_int_distribution<int> distribution(0, 255);

    vector<ByteString> l(n);
    for (int i = 0; i < n; i++) {
      shared_ptr<vector<uint8>> bytes { new vector<uint8>(len) };
      for (int j = 0; j < len; j++) {
        (*bytes)[j] = (uint8) distribution(gen);
      }
      l[i] = ByteString(bytes);
    }
    return l;
  }

  vector<ByteString> RandomKeys(int n, int seed) {
    return RandomSeqs(n, seed, 20);
  }

  vector<ByteString> RandomValues(int n, int seed) {
    return RandomSeqs(n, seed, 400);
  }

  vector<ByteString> RandomSortedKeys(int n, int seed) {
    vector<ByteString> data = RandomKeys(n, seed);
    std::sort(data.begin(), data.end());
    return data;
  }

  pair<vector<ByteString>, vector<ByteString>> RandomQueryKeysAndValues(
      int n, int seed,
      vector<ByteString> const& insertedKeys,
      vector<ByteString> const& insertedValues)
  {
    std::default_random_engine gen;
    gen.seed(seed);
    std::uniform_int_distribution<int> rand_bool(0, 1);
    std::uniform_int_distribution<int> rand_byte(0, 255);
    std::uniform_int_distribution<int> rand_idx(0, insertedKeys.size() - 1);
    
    shared_ptr<vector<uint8>> emptyBytesVec { new vector<uint8>(0) };
    ByteString emptyBytes(emptyBytesVec);

    vector<ByteString> queryKeys(n);
    vector<ByteString> queryValues(n);

    for (int i = 0; i < n; i++) {
      if (rand_bool(gen) == 0) {
        // Min length 20 so probability of collision is miniscule
        shared_ptr<vector<uint8>> bytes { new vector<uint8>(20) };
        for (int j = 0; j < emptyBytesVec->size(); j++) {
          (*bytes)[j] = rand_byte(gen);
        }
        queryKeys[i] = ByteString(bytes);
        queryValues[i] = emptyBytes;
      } else {
        int idx = rand_idx(gen);
        queryKeys[i] = insertedKeys[idx];
        queryValues[i] = insertedValues[idx];
      }
    }

    return make_pair(move(queryKeys), move(queryValues));
  }
};

class BenchmarkRandomInserts : public Benchmark {
public:
  int count = 50;

  virtual string name() override { return "RandomInserts"; }
  virtual int opCount() override { return count; }

  vector<ByteString> keys;
  vector<ByteString> values;

  BenchmarkRandomInserts() {
    int seed1 = 1234;
    int seed2 = 527;
    keys = RandomKeys(count, seed1);
    values = RandomValues(count, seed2);
  }

  virtual void prepare(Application& app) override {
  }
  virtual void go(Application& app) override {
    for (int i = 0; i < keys.size(); i++) {
      app.Insert(keys[i], values[i]);
    }
    app.Sync();
  }
};

class BenchmarkRandomQueries : public Benchmark {
public:
  int count = 50;

  virtual string name() override { return "RandomQueries"; }
  virtual int opCount() override { return count; }

  vector<ByteString> keys;
  vector<ByteString> values;
  vector<ByteString> query_keys;
  vector<ByteString> query_values;

  BenchmarkRandomQueries() {
    int seed1 = 1234;
    int seed2 = 527;
    int seed3 = 19232;
    keys = RandomKeys(count, seed1);
    values = RandomValues(count, seed2);

    auto p = RandomQueryKeysAndValues(count, seed3, keys, values);
    query_keys = move(p.first);
    query_values = move(p.second);
  }

  virtual void prepare(Application& app) override {
    for (int i = 0; i < keys.size(); i++) {
      app.Insert(keys[i], values[i]);
    }
    app.Sync();
    app.crash();
  }
  virtual void go(Application& app) override {
    for (int i = 0; i < query_keys.size(); i++) {
      app.QueryAndExpect(query_keys[i], query_values[i]);
    }
  }
};

void RunAllBenchmarks() {
  { BenchmarkRandomInserts q; q.run(); }
  { BenchmarkRandomQueries q; q.run(); }
}

shared_ptr<Benchmark> benchmark_by_name(string const& name) {
  if (name == "random-queries") { return shared_ptr<Benchmark>(new BenchmarkRandomQueries()); }
  if (name == "random-inserts") { return shared_ptr<Benchmark>(new BenchmarkRandomInserts()); }

  cerr << "No benchmark found by name " << name << endl;
  exit(1);
}

void RunBenchmark(string const& name) {
  benchmark_by_name(name)->run();
}
