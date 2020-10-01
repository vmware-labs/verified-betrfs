#include <stdio.h>
#include "stataccounting.h"

namespace StatAccounting {

void report() {
    FILE* fp;
    char line[1000];
    fp = fopen("/proc/self/stat", "r");
    fgets(line, sizeof(line), fp);
    fclose(fp);

// The following block is the output of ycsb/parse-proc.py
    long unsigned utime;
    long unsigned stime;
    long unsigned vsize;
    long rss;
    sscanf(line, "%*d %*s %*c %*d %*d %*d %*d %*d %*u %*u %*u %*u %*u %lu %lu %*d %*d %*d %*d %*d %*d %*u %lu %ld %*u %*u %*u %*u %*u %*u %*u %*u %*u %*u %*u %*u %*u %*d %*d %*u %*u %*u %*u %*d %*u %*u %*u %*u %*u %*u %*u %*d", &utime, &stime, &vsize, &rss);

    printf("stat-accounting utime %lu stime %lu vsize %lu rss %ld\n",
       utime, stime, vsize, rss);
}

} // namespace StatAccounting
