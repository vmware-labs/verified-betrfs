#include "Application.h"

#define ROW_CACHE_SIZE (1 << 18)

using namespace std;


RowCache::RowCache() : head(-1), tail(-1)
{
  queue.resize(ROW_CACHE_SIZE);
}

optional<ByteString> RowCache::get(ByteString key)
{
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

void RowCache::set(ByteString key, ByteString val)
{
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
