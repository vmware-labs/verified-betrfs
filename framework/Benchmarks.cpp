#include "Benchmarks.h"

#include <chrono>
#include <iostream>
#include <random>
#include <algorithm>
#include <cstdio>
#include <cassert>

#include "Application.h"

using namespace std;

void benchmark_start(string const& name);
void benchmark_end(string const& name);

constexpr int KEY_SIZE = 20;
constexpr int VALUE_SIZE = 400;

class Benchmark {
public:
  virtual ~Benchmark() {}

  virtual string name() = 0;
  virtual int opCount() = 0;
  virtual void prepare(Application& app) = 0;
  virtual void go(Application& app) = 0;

  void run(string filename, bool skipPrepare = false) {
    if (!skipPrepare) {
      Mkfs(filename);
    }

    Application app(filename);

    if (!skipPrepare) {
      prepare(app);
    }

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
    return RandomSeqs(n, seed, KEY_SIZE);
  }

  vector<ByteString> RandomValues(int n, int seed) {
    return RandomSeqs(n, seed, VALUE_SIZE);
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
        for (size_t j = 0; j < bytes.size(); j++) {
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
    for (size_t i = 0; i < b.size(); i++) {
      uint8 by = b.seq.select(i);
      int x = by >> 4;
      int y = by & 0xf;
      ch[2*i] = (x < 10 ? x + '0' : x + 'a' - 10);
      ch[2*i + 1] = (y < 10 ? y + '0' : y + 'a' - 10);
    }
    return string(&ch[0], ch.size());
  }
};

class SimpleTest : public Benchmark {
public:
  virtual string name() override { return "SimpleTest"; }
  virtual int opCount() override { return 100000; }

  SimpleTest() {
  }

  virtual void prepare(Application& app) override {
    app.Insert("a", "1");
    app.Insert("b", "2");
    app.Insert("c", "3");
    app.Insert("d", "4");
    app.Sync(true);
    app.crash();
  }
  virtual void go(Application& app) override {
    app.QueryAndExpect(ByteString("a"), ByteString("1"));
    app.QueryAndExpect(ByteString("b"), ByteString("2"));
    app.QueryAndExpect(ByteString("c"), ByteString("3"));
    app.QueryAndExpect(ByteString("d"), ByteString("4"));
    app.QueryAndExpect(ByteString("a"), ByteString("1"));
    app.QueryAndExpect(ByteString("b"), ByteString("2"));
    app.QueryAndExpect(ByteString("c"), ByteString("3"));
    app.QueryAndExpect(ByteString("d"), ByteString("4"));
    app.QueryAndExpect(ByteString("a"), ByteString("1"));
    app.QueryAndExpect(ByteString("a"), ByteString("1"));
    app.QueryAndExpect(ByteString("a"), ByteString("1"));
    app.QueryAndExpect(ByteString("b"), ByteString("2"));
    app.QueryAndExpect(ByteString("a"), ByteString("1"));
    app.QueryAndExpect(ByteString("b"), ByteString("2"));
    app.QueryAndExpect(ByteString("c"), ByteString("3"));
    app.QueryAndExpect(ByteString("d"), ByteString("4"));
    app.QueryAndExpect(ByteString("a"), ByteString("1"));
    app.QueryAndExpect(ByteString("c"), ByteString("3"));
    app.QueryAndExpect(ByteString("a"), ByteString("1"));
    app.QueryAndExpect(ByteString("a"), ByteString("1"));
    app.QueryAndExpect(ByteString("a"), ByteString("1"));

    app.QueryAndExpect(ByteString("a"), ByteString("1"));
    app.QueryAndExpect(ByteString("b"), ByteString("2"));
    app.QueryAndExpect(ByteString("c"), ByteString("3"));
    app.QueryAndExpect(ByteString("d"), ByteString("4"));

    app.Insert("a", "x");

    app.QueryAndExpect(ByteString("a"), ByteString("x"));
    app.QueryAndExpect(ByteString("b"), ByteString("2"));
    app.QueryAndExpect(ByteString("c"), ByteString("3"));
    app.QueryAndExpect(ByteString("d"), ByteString("4"));

    app.Insert("b", "y");

    app.QueryAndExpect(ByteString("d"), ByteString("4"));
    app.QueryAndExpect(ByteString("c"), ByteString("3"));
    app.QueryAndExpect(ByteString("b"), ByteString("y"));
    app.QueryAndExpect(ByteString("a"), ByteString("x"));

    app.QueryAndExpect(ByteString("a"), ByteString("x"));
    app.QueryAndExpect(ByteString("b"), ByteString("y"));
    app.QueryAndExpect(ByteString("c"), ByteString("3"));
    app.QueryAndExpect(ByteString("d"), ByteString("4"));

    app.Insert("c", "z");

    app.QueryAndExpect(ByteString("d"), ByteString("4"));
    app.QueryAndExpect(ByteString("c"), ByteString("z"));
    app.QueryAndExpect(ByteString("b"), ByteString("y"));
    app.QueryAndExpect(ByteString("a"), ByteString("x"));

    app.QueryAndExpect(ByteString("a"), ByteString("x"));
    app.QueryAndExpect(ByteString("b"), ByteString("y"));
    app.QueryAndExpect(ByteString("c"), ByteString("z"));
    app.QueryAndExpect(ByteString("d"), ByteString("4"));

    app.Insert("d", "w");

    app.QueryAndExpect(ByteString("d"), ByteString("w"));
    app.QueryAndExpect(ByteString("c"), ByteString("z"));
    app.QueryAndExpect(ByteString("b"), ByteString("y"));
    app.QueryAndExpect(ByteString("a"), ByteString("x"));

    app.QueryAndExpect(ByteString("a"), ByteString("x"));
    app.QueryAndExpect(ByteString("b"), ByteString("y"));
    app.QueryAndExpect(ByteString("c"), ByteString("z"));
    app.QueryAndExpect(ByteString("d"), ByteString("w"));

    ByteString t[4];
    t[0] = ByteString("x");
    t[1] = ByteString("y");
    t[2] = ByteString("z");
    t[3] = ByteString("w");
    for (int i = 0; i < 100000; i++) {
      int k = rand() % 4;
      ByteString key;
      if (k == 0) key = ByteString("a");
      if (k == 1) key = ByteString("b");
      if (k == 2) key = ByteString("c");
      if (k == 3) key = ByteString("d");
      if (rand() % 2) {
        app.QueryAndExpect(key, t[k]);
      } else {
        int v = rand() % 2;
        ByteString val;
        if (k == 0) val = v ? ByteString("1") : ByteString("11");
        if (k == 1) val = v ? ByteString("2") : ByteString("22");
        if (k == 2) val = v ? ByteString("3") : ByteString("33");
        if (k == 3) val = v ? ByteString("4") : ByteString("44");
        app.Insert(key, val);
        t[k] = val;
      }
    }
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
    for (size_t i = 0; i < keys.size(); i++) {
      app.Insert(keys[i], values[i]);
    }
    app.Sync(false);
  }
};

class BenchmarkLongRandomInserts : public Benchmark {
public:
  int count = 5000000;

  virtual string name() override { return "LongRandomInserts"; }
  virtual int opCount() override { return count; }

  uint32_t rngState = 198432;

  uint32_t NextPseudoRandom() {
    rngState = (uint32_t) (((uint64_t) rngState * 279470273) % 0xfffffffb);
    return rngState;
  }

  BenchmarkLongRandomInserts() {
  }

  virtual void prepare(Application& app) override {
  }

  virtual void go(Application& app) override {
    static_assert (KEY_SIZE % 4 == 0, "");
    static_assert (VALUE_SIZE % 4 == 0, "");

    for (int i = 0; i < count; i++) {
      ByteString key(KEY_SIZE);
      for (int j = 0; j < KEY_SIZE; j += 4) {
        uint32_t* ptr = (uint32_t*) (key.seq.ptr() + j);
        *ptr = NextPseudoRandom();
      }
      ByteString value(VALUE_SIZE);
      for (int j = 0; j < VALUE_SIZE; j += 4) {
        uint32_t* ptr = (uint32_t*) (value.seq.ptr() + j);
        *ptr = NextPseudoRandom();
      }

      app.Insert(key, value);

      if (i % 50000 == 0) app.Sync(false);
    }

    app.Sync(true);
  }
};

class BenchmarkBigTreeQueries : public Benchmark {
public:
  int insertCount = 5000000;
  int queryCount  =    2000;

  virtual string name() override { return "BigTreeQueries"; }
  virtual int opCount() override { return queryCount; }

  uint32_t rngState;

  void resetRng() {
    rngState = 198432;
  }

  vector<ByteString> queryKeys;
  vector<ByteString> queryValues;

  uint32_t NextPseudoRandom() {
    rngState = (uint32_t) (((uint64_t) rngState * 279470273) % 0xfffffffb);
    return rngState;
  }

  BenchmarkBigTreeQueries() {
    resetRng();

    for (int i = 0; i < queryCount; i++) {
      ByteString key(KEY_SIZE);
      ByteString value(VALUE_SIZE);

      for (int k = 0; k < insertCount / queryCount; k++) {
        for (int j = 0; j < KEY_SIZE; j += 4) {
          uint32_t* ptr = (uint32_t*) (key.seq.ptr() + j);
          *ptr = NextPseudoRandom();
        }
        for (int j = 0; j < VALUE_SIZE; j += 4) {
          uint32_t* ptr = (uint32_t*) (value.seq.ptr() + j);
          *ptr = NextPseudoRandom();
        }
      }

      queryKeys.push_back(key);
      queryValues.push_back(value);
    }
  }

  virtual void prepare(Application& app) override {
    static_assert (KEY_SIZE % 4 == 0, "");
    static_assert (VALUE_SIZE % 4 == 0, "");

    resetRng();

    for (int i = 0; i < insertCount; i++) {
      ByteString key(KEY_SIZE);
      for (int j = 0; j < KEY_SIZE; j += 4) {
        uint32_t* ptr = (uint32_t*) (key.seq.ptr() + j);
        *ptr = NextPseudoRandom();
      }
      ByteString value(VALUE_SIZE);
      for (int j = 0; j < VALUE_SIZE; j += 4) {
        uint32_t* ptr = (uint32_t*) (value.seq.ptr() + j);
        *ptr = NextPseudoRandom();
      }

      app.Insert(key, value);
    }
    app.Sync(true);
    app.crash();
  }

  virtual void go(Application& app) override {
    for (int i = 0; i < queryCount; i++) {
      app.QueryAndExpect(queryKeys[i], queryValues[i]);
    }
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
    for (size_t i = 0; i < keys.size(); i++) {
      app.Insert(keys[i], values[i]);
    }
    app.Sync(true);
    app.crash();
  }
  virtual void go(Application& app) override {
    for (size_t i = 0; i < query_keys.size(); i++) {
      app.QueryAndExpect(query_keys[i], query_values[i]);
    }
  }
};

class BenchmarkMixedInsertQuery : public Benchmark {
public:
  int start = 1000000;
  int count = 5000000;

  int KEY_SIZE = 24;
  int VALUE_SIZE = 512;

  virtual string name() override { return "MixedInsertQuery"; }
  virtual int opCount() override { return count; }

  uint32_t rngState = 198432;

  uint32_t NextPseudoRandom() {
    rngState = (uint32_t) (((uint64_t) rngState * 279470273) % 0xfffffffb);
    return rngState;
  }

  vector<ByteString> keys;

  BenchmarkMixedInsertQuery() {
    for (int i = 0; i < start + count/2; i++) {
      ByteString key(KEY_SIZE);
      for (int j = 0; j < KEY_SIZE; j += 4) {
        uint32_t* ptr = (uint32_t*) (key.seq.ptr() + j);
        *ptr = NextPseudoRandom();
      }
      keys.push_back(key);
    }
  }

  virtual void prepare(Application& app) override {
    for (int i = 0; i < start; i++) {
      ByteString value(VALUE_SIZE);
      for (int j = 0; j < VALUE_SIZE; j += 4) {
        uint32_t* ptr = (uint32_t*) (value.seq.ptr() + j);
        *ptr = NextPseudoRandom();
      }

      app.Insert(keys[i], value);
    }

    app.Sync(true);
  }

  virtual void go(Application& app) override {
    assert (KEY_SIZE % 4 == 0);
    assert (VALUE_SIZE % 4 == 0);

    rngState = 43211;

    for (int i = 0; i < count; i++) {
      if (i % 10000 == 0)  cout << i << endl;

      if (i % 2) {
        int v = NextPseudoRandom() % keys.size();
        app.Query(keys[v]);
      } else {
        int key_idx = start + i / 2;
        ByteString value(VALUE_SIZE);
        for (int j = 0; j < VALUE_SIZE; j += 4) {
          uint32_t* ptr = (uint32_t*) (value.seq.ptr() + j);
          *ptr = NextPseudoRandom();
        }
        app.Insert(keys[key_idx], value);
      }
    }
  }
};

class BenchmarkMixedUpdateQuery : public Benchmark {
public:
  int start = 1000000;
  int count = 5000000;

  // match ycsb-a
  int KEY_SIZE = 24;
  int VALUE_SIZE = 512;

  virtual string name() override { return "MixedUpdateQuery"; }
  virtual int opCount() override { return count; }

  uint32_t rngState = 198432;

  uint32_t NextPseudoRandom() {
    rngState = (uint32_t) (((uint64_t) rngState * 279470273) % 0xfffffffb);
    return rngState;
  }

  vector<ByteString> keys;

  BenchmarkMixedUpdateQuery() {
    for (int i = 0; i < start; i++) {
      ByteString key(KEY_SIZE);
      for (int j = 0; j < KEY_SIZE; j += 4) {
        uint32_t* ptr = (uint32_t*) (key.seq.ptr() + j);
        *ptr = NextPseudoRandom();
      }
      keys.push_back(key);
    }
  }

  virtual void prepare(Application& app) override {
    for (int i = 0; i < start; i++) {
      ByteString value(VALUE_SIZE);
      for (int j = 0; j < VALUE_SIZE; j += 4) {
        uint32_t* ptr = (uint32_t*) (value.seq.ptr() + j);
        *ptr = NextPseudoRandom();
      }

      app.Insert(keys[i], value);
    }

    app.Sync(true);
  }

  virtual void go(Application& app) override {
    assert (KEY_SIZE % 4 == 0);
    assert (VALUE_SIZE % 4 == 0);

    rngState = 43211;

    for (int i = 0; i < count; i++) {
      if (i % 10000 == 0)  cout << i << endl;

      if (i % 2) {
        int v = NextPseudoRandom() % keys.size();
        app.Query(keys[v]);
      } else {
        int key_idx = NextPseudoRandom() % keys.size();
        ByteString value(VALUE_SIZE);
        for (int j = 0; j < VALUE_SIZE; j += 4) {
          uint32_t* ptr = (uint32_t*) (value.seq.ptr() + j);
          *ptr = NextPseudoRandom();
        }
        app.Insert(keys[key_idx], value);
      }
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

  size_t targetCount = 100;

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
    for (size_t i = 0; i < queries.size(); i++) {
      int idx = get_first_idx_ge(keys_values, queries[i]);
      vector<pair<ByteString, ByteString>> query_result;
      while (query_result.size() < targetCount && idx < (int)keys_values.size()) {
        query_result.push_back(keys_values[idx]);
        idx++;
      }
      query_results.push_back(move(query_result));
    }
  }

  virtual void prepare(Application& app) override {
    for (size_t i = 0; i < keys_values.size(); i++) {
      //cout << "Inserting " << to_hex(keys_values[i].first) << " -> " << to_hex(keys_values[i].second) << endl;
      app.Insert(keys_values[i].first, keys_values[i].second);
    }
    app.Sync(true);
    app.crash();
  }

  virtual void go(Application& app) override {
    for (size_t i = 0; i < queries.size(); i++) {
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
    app.Sync(true);
  }
};

class BenchmarkReplay : public Benchmark {
public:
  int count = 20000;

  virtual string name() override { return "Replay"; }
  virtual int opCount() override { return 1; }

  vector<ByteString> keys;
  vector<ByteString> values;
  vector<ByteString> query_keys;
  vector<ByteString> query_values;

  BenchmarkReplay() {
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
    for (size_t i = 0; i < keys.size(); i++) {
      app.Insert(keys[i], values[i]);
    }
    app.Sync(false);
    app.crash();
  }
  virtual void go(Application& app) override {
    app.QueryAndExpect(query_keys[0], query_values[0]);
  }
};

void RunAllBenchmarks(string filename) {
  { BenchmarkRandomInserts q; q.run(filename); }
  { BenchmarkRandomQueries q; q.run(filename); }
  { BenchmarkRandomSuccQueries q; q.run(filename); }
}

shared_ptr<Benchmark> benchmark_by_name(string const& name) {
  if (name == "random-queries") { return shared_ptr<Benchmark>(new BenchmarkRandomQueries()); }
  if (name == "random-inserts") { return shared_ptr<Benchmark>(new BenchmarkRandomInserts()); }
  if (name == "long-random-inserts") { return shared_ptr<Benchmark>(new BenchmarkLongRandomInserts()); }
  if (name == "big-tree-queries") { return shared_ptr<Benchmark>(new BenchmarkBigTreeQueries()); }
  if (name == "random-succs") { return shared_ptr<Benchmark>(new BenchmarkRandomSuccQueries()); }
  if (name == "mixed-insert-query") { return shared_ptr<Benchmark>(new BenchmarkMixedInsertQuery()); }
  if (name == "mixed-update-query") { return shared_ptr<Benchmark>(new BenchmarkMixedUpdateQuery()); }
  if (name == "replay") { return shared_ptr<Benchmark>(new BenchmarkReplay()); }
  if (name == "simple-test") { return shared_ptr<Benchmark>(new SimpleTest()); }

  cerr << "No benchmark found by name " << name << endl;
  exit(1);
}

class StopwatchEntry {
public:
  long long ns;
  bool in_progress;
  int count;
  std::chrono::time_point<std::chrono::high_resolution_clock> last;

  StopwatchEntry() {
    ns = 0;
    in_progress = false;
    count = 0;
  }

  void start() {
    assert(!in_progress);
    in_progress = true;
    last = chrono::high_resolution_clock::now();
  }

  void end() {
    assert(in_progress);
    in_progress = false;
    auto t2 = chrono::high_resolution_clock::now();
    ns += std::chrono::duration_cast<std::chrono::nanoseconds>(t2 - last).count();
    count++;
  }

  void append(long long ns) {
    this->ns += ns;
    count++;
  }
};
map<string, StopwatchEntry> sw;

string nameToString(DafnySequence<char> dafnyName) {
  return string(dafnyName.ptr(), dafnyName.size());
}

void benchmark_start(string const& name) {
  auto it = sw.find(name);
  if (it == sw.end()) {
    sw.insert(make_pair(name, StopwatchEntry()));
  }
  sw[name].start();
}

void benchmark_end(string const& name) {
  sw[name].end();
}

void benchmark_append(string const& name, long long ns) {
  auto it = sw.find(name);
  if (it == sw.end()) {
    sw.insert(make_pair(name, StopwatchEntry()));
  }
  sw[name].append(ns);
}

void benchmark_dump() {
  for (auto& p : sw) {
    string name = p.first;
    int count = p.second.count;
    long long ms = p.second.ns / 1000000;
    cout << name << " " << ms << " ms, " << count << " ticks" << endl;
  }
}

void benchmark_clear() {
  sw.clear();
}

namespace NativeBenchmarking_Compile {
  void start(DafnySequence<char> dafnyName) {
    benchmark_start(nameToString(dafnyName));
  }

  void end(DafnySequence<char> dafnyName) {
    benchmark_end(nameToString(dafnyName));
  }
}

void RunBenchmark(string filename, string const& name, bool skipPrepare) {
  benchmark_by_name(name)->run(filename, skipPrepare);
  benchmark_dump();
}
