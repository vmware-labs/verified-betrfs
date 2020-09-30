#include <unistd.h> // debug
#include "Application.h"

//#define ROW_CACHE_SIZE (1 << 18)

using namespace std;

unsigned long ROW_CACHE_SIZE = 0;

RowCache::RowCache() : head(-1), tail(-1)
{
  ROW_CACHE_SIZE = atoi(getenv("ROW_CACHE_SIZE"));
  printf("metadata ROW_CACHE_SIZE %lu\n", ROW_CACHE_SIZE);
  if (ROW_CACHE_SIZE == 0) { return; }

  queue.resize(ROW_CACHE_SIZE);
}

void jonh_debug(int set_incr, int get_incr) {
    static int set_count = 0;
    static int get_count = 0;
    set_count += set_incr;
    get_count += get_incr;
    if ((set_count + get_count) %100000 == 0) {
        char cmd[1024];
        sprintf(cmd, "grep VmSize /proc/%d/status", getpid());
        system(cmd);
        printf("set_count %d get_count %d\n", set_count, get_count);
        fflush(stdout);
    }
}

optional<ByteString> RowCache::get(ByteString key)
{
  if (ROW_CACHE_SIZE == 0) { return; }

  jonh_debug(0, 1);
  fflush(stdout);

  auto iter = m.find(key);
  if (iter == m.end()) {
    return nullopt;
  } else {
    int idx = iter->second;

    if (queue[idx].prev != -1) {
      int prev = queue[idx].prev;
      int next = queue[idx].next;

      queue[idx].prev = -1;
      queue[idx].next = this->head;
      queue[head].prev = idx;
      this->head = idx;
      queue[prev].next = next;
      if (next == -1) {
        tail = prev;
      } else {
        queue[next].prev = prev;
      }
    }

    return optional<ByteString>(queue[idx].value);
  }
}

void RowCache::set(ByteString in_key, ByteString in_val)
{
  if (ROW_CACHE_SIZE == 0) { return; }

  jonh_debug(1, 0);
  // The input are substrings of big Dafny strings. Copy out the values
  // to avoid keeping a 1MB string alive behind every 500-byte val we tuck
  // into this cache.
  ByteString key = ByteString(in_key.as_string());
  ByteString val = ByteString(in_val.as_string());

  auto iter = m.find(key);
  if (iter == m.end()) {
    if (m.size() < ROW_CACHE_SIZE) {
      int idx = m.size();
      m.insert(make_pair(key, idx));
      queue[idx].key = key;
      queue[idx].value = val;
      queue[idx].prev = -1;
      queue[idx].next = head;
      if (head != -1) {
        queue[head].prev = idx;
      }
      this->head = idx;
      if (idx == 0) {
        this->tail = 0;
      }
    } else {
      // Overwrite the tail element
      int idx = tail;
      m.erase(queue[idx].key);
      m.insert(make_pair(key, idx));
      int prev = queue[idx].prev;
      queue[prev].next = -1;
      tail = prev;
      queue[idx].key = key;
      queue[idx].value = val;
      queue[idx].prev = -1;
      queue[idx].next = head;
      queue[head].prev = idx;
      head = idx;
    }
  } else {
    int idx = iter->second;
    queue[idx].value = val;
    int prev = queue[idx].prev;
    int next = queue[idx].next;
    if (prev != -1) {
      queue[idx].prev = -1;
      queue[idx].next = this->head;
      queue[head].prev = idx;
      this->head = idx;
      queue[prev].next = next;
      if (next == -1) {
        tail = prev;
      } else {
        queue[next].prev = prev;
      }
    }
  }
}
