#include <iostream>
#include <fstream>
using namespace std;

// To free pagecache:
// echo 1 > /proc/sys/vm/drop_caches
//
// To free dentries and inodes:
// echo 2 > /proc/sys/vm/drop_caches
//
// To free pagecache, dentries and inodes:
// echo 3 > /proc/sys/vm/drop_caches

int main() {
  ofstream drop_caches;
  drop_caches.open("/proc/sys/vm/drop_caches");
  drop_caches << "3" << endl;
  drop_caches.close();
}
