#!/usr/bin/env python3
import numpy as np
#linear = np.mean([75.579, 75.632, 78.823])
linear = np.mean([ 39.850, 39.069, 39.436, 38.203, 37.962, ])
manual_tail_recursion = np.mean([ 25.036, 25.055, 24.524, 24.351, 24.613, ])
#repr =np.mean([ 31.879, 32.656, 30.160, 29.820, 29.796, ])
repr =np.mean([ 29.076, 29.172, 27.810, 29.109, 28.811, ])

print("linear %.1fs"% linear)
print("manual_tail_recursion  %.1fs"% manual_tail_recursion  )
print("repr %.1fs"% repr)
print("ratio: %.2fs" % (linear/repr))
print("ratio: %.2fs" % (manual_tail_recursion  /repr))
