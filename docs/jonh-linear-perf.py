#!/usr/bin/env python3
import numpy as np
import matplotlib.pyplot as plt
from math import log
#linear = np.mean([75.579, 75.632, 78.823])
linear = np.mean([ 39.850, 39.069, 39.436, 38.203, 37.962, ])
linear_no_locks = np.mean([ 39.768, 39.853 ])
manual_tail_recursion = np.mean([ 25.036, 25.055, 24.524, 24.351, 24.613, ])
#repr =np.mean([ 31.879, 32.656, 30.160, 29.820, 29.796, ])
repr =np.mean([ 29.076, 29.172, 27.810, 29.109, 28.811, ])
# repr_no_locks is g++ with -D_LIBCPP_HAS_NO_THREADS
repr_no_locks = np.mean([ 29.696, 29.940 ])

print("linear %.1fs"% linear)
print("manual_tail_recursion  %.1fs"% manual_tail_recursion  )
print("repr %.1fs"% repr)
print("ratio: %.2fs" % (linear/repr))
print("ratio: %.2fs" % (manual_tail_recursion  /repr))
print("ratio: %.2fs" % (manual_tail_recursion  /linear))
print("")

linear_clang_no_locks = np.mean([ 23.909, 24.278, 23.766 ])
linear_clang_no_locks_borrow = np.mean([ 23.016, 23.535, 22.770 ])
repr_clang_no_locks = np.mean([ 23.507, 23.259, 24.489 ])
print("clang ratio: %.2fs" % (linear_clang_no_locks  / repr_clang_no_locks))
print("clang ratio: %.2fs" % (linear_clang_no_locks_borrow  / repr_clang_no_locks))

linear_no_locks_32 = np.mean([ 46.260 ])
linear_no_locks_16 = np.mean([ 54.461 ])
linear_no_locks_8 = np.mean([ 78.249 ])
linear_no_locks_4 = np.mean([ 136.412 ])

linear_clang_no_locks = {
    64: np.mean([ 25.753, 24.784 ]),
    32: np.mean([ 23.9 ]),
    16: np.mean([ 26.027 ]),
    8: np.mean([ 30.649 ]),
    4: np.mean([ 49.4 ]),
}

linear_clang_no_locks_borrow = {
    64: np.mean([ 24.091 ]),
    32: np.mean([ 22.207, 21.895 ]),
    16: np.mean([ 24.595, 24.924 ]),
    8: np.mean([ 26.830 ]),
    4: np.mean([ 41.634, 41.105 ]),
}
fig, axis = plt.subplots(1)
line, = axis.plot(list(linear_clang_no_locks.keys()), list(linear_clang_no_locks.values()))
line.set_label("linear_clang_no_locks")
line, = axis.plot(list(linear_clang_no_locks_borrow.keys()), list(linear_clang_no_locks_borrow.values()))
line.set_label("linear_clang_no_locks_borrow")
for x in linear_clang_no_locks_borrow.keys():
    y = linear_clang_no_locks[x]
    ovh = (linear_clang_no_locks[x] - linear_clang_no_locks_borrow[x]) / linear_clang_no_locks[x]
    axis.text(x, y, "%.1f%%" % (ovh*100))
    axis.text(x, y*0.8, "%.1f" % (log(10000000)/log(x)))
axis.text(64, repr_clang_no_locks, "* Repr no locks")
axis.set_ylim(bottom=0)
axis.legend()
axis.set_ylabel("runtime (s)")
axis.set_title("10M inserts")
axis.set_xlabel("branching factor")
axis.set_xticks(list(linear_clang_no_locks.keys()))
plt.savefig("borrow.png")
