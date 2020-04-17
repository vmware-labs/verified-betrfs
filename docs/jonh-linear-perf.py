#!/usr/bin/env python3
import numpy as np
#linear = np.mean([75.579, 75.632, 78.823])
linear = np.mean([ 39.850, 39.069, 39.436, 38.203, 37.962, ])
repr =np.mean([ 31.879, 32.656, 30.160, 29.820, 29.796, ])
print("linear %.1fs"% linear)
print("repr %.1fs"% repr)
print("ratio: %.2fs" % (linear/repr))
