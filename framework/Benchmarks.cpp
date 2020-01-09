#include "Benchmarks.h"

#include <chrono>
#include <iostream>
#include <random>
#include <algorithm>
#include <cstdio>

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
      l[i] = ByteString(len);
      for (int j = 0; j < len; j++) {
        l[i].seq.ptr()[j] = (uint8) distribution(gen);
      }
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
    
    ByteString emptyBytes(0);

    vector<ByteString> queryKeys(n);
    vector<ByteString> queryValues(n);

    for (int i = 0; i < n; i++) {
      if (rand_bool(gen) == 0) {
        // Min length 20 so probability of collision is miniscule
        ByteString bytes(20);
        for (int j = 0; j < bytes.size(); j++) {
          bytes.seq.ptr()[j] = rand_byte(gen);
        }
        queryKeys[i] = bytes;
        queryValues[i] = emptyBytes;
      } else {
        int idx = rand_idx(gen);
        queryKeys[i] = insertedKeys[idx];
        queryValues[i] = insertedValues[idx];
      }
    }

    return make_pair(move(queryKeys), move(queryValues));
  }

  [[ noreturn ]]
  void fail(string err)
  {
    cout << "fatal error: " << err << endl;
    exit(1);
  }

  string to_hex(ByteString const& b) {
    vector<char> ch(b.size() * 2);
    for (int i = 0; i < b.size(); i++) {
      uint8 by = b.seq.select(i);
      int x = by >> 4;
      int y = by & 0xf;
      ch[2*i] = (x < 10 ? x + '0' : x + 'a' - 10);
      ch[2*i + 1] = (y < 10 ? y + '0' : y + 'a' - 10);
    }
    return string(&ch[0], ch.size());
  }
};

class BenchmarkRandomInserts : public Benchmark {
public:
  int count = 500000;

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
  int count = 500000;

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

int get_first_idx_ge(vector<pair<ByteString, ByteString>> const& v, ByteString key)
{
  int lo = 0;
  int hi = v.size() + 1;
  while (hi > lo + 1) {
    int mid = (lo + hi) / 2;
    if (v[mid-1].first < key) {
      lo = mid;
    } else {
      hi = mid;
    }
  }
  return lo;
}

class BenchmarkRandomSuccQueries : public Benchmark {
public:
  int insertCount = 50000;
  int queryCount = 1000;

  int targetCount = 100;

  virtual string name() override { return "RandomSuccQueries"; }
  virtual int opCount() override { return queryCount; }

  vector<pair<ByteString, ByteString>> keys_values;
  vector<ByteString> queries;
  vector<vector<pair<ByteString, ByteString>>> query_results;

  BenchmarkRandomSuccQueries() {
    int seed1 = 1234;
    int seed2 = 527;
    int seed3 = 9001;
    vector<ByteString> keys = RandomKeys(insertCount, seed1);
    vector<ByteString> values = RandomValues(insertCount, seed2);
    sort(keys.begin(), keys.end());
    for (int i = 0; i < insertCount; i++) {
      keys_values.push_back(make_pair(keys[i], values[i]));
    }

    queries = RandomKeys(queryCount, seed3);
    for (int i = 0; i < queries.size(); i++) {
      int idx = get_first_idx_ge(keys_values, queries[i]);
      vector<pair<ByteString, ByteString>> query_result;
      while (query_result.size() < targetCount && idx < keys_values.size()) {
        query_result.push_back(keys_values[idx]);
        idx++;
      }
      query_results.push_back(move(query_result));
    }
  }

  virtual void prepare(Application& app) override {
    for (int i = 0; i < keys_values.size(); i++) {
      //cout << "Inserting " << to_hex(keys_values[i].first) << " -> " << to_hex(keys_values[i].second) << endl;
      app.Insert(keys_values[i].first, keys_values[i].second);
    }
    app.Sync();
    app.crash();
  }

  virtual void go(Application& app) override {
    for (int i = 0; i < queries.size(); i++) {
      auto result = app.Succ(queries[i], true /* inclusive */, targetCount);
      if (result != query_results[i]) {
        cout << "query " << to_hex(queries[i]) << endl;
        cout << "result: " << endl;
        for (auto p : result) {
          cout << "    " << to_hex(p.first) << " : " << to_hex(p.second) << endl;
        }
        cout << "expected result: " << endl;
        for (auto p : query_results[i]) {
          cout << "    " << to_hex(p.first) << " : " << to_hex(p.second) << endl;
        }
        fail("Incorrect succ result");
      }
    }
    app.Sync();
  }
};


void RunAllBenchmarks() {
  { BenchmarkRandomInserts q; q.run(); }
  { BenchmarkRandomQueries q; q.run(); }
  { BenchmarkRandomSuccQueries q; q.run(); }
}

shared_ptr<Benchmark> benchmark_by_name(string const& name) {
  if (name == "random-queries") { return shared_ptr<Benchmark>(new BenchmarkRandomQueries()); }
  if (name == "random-inserts") { return shared_ptr<Benchmark>(new BenchmarkRandomInserts()); }
  if (name == "random-succs") { return shared_ptr<Benchmark>(new BenchmarkRandomSuccQueries()); }

  cerr << "No benchmark found by name " << name << endl;
  exit(1);
}

void RunBenchmark(string const& name) {
  benchmark_by_name(name)->run();
}
