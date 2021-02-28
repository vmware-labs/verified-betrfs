#!/usr/bin/env python3

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause


import matplotlib.pyplot as plt

class System:
    def __init__(self, name, impl, proof):
        self.name = name
        self.impl = impl
        self.proof = proof

systems = [
    System("seL4", 8700+600, 4900+13000+15000+110000+55000),
    System("veribetrfs", 6119, 28366),
    System("fscq", 3000, 30000),    # impl numbers not in paper; 3000 is paper's claim for comparable xv6
    # dfscq likewise lists 84kloc, but doesn't separate code from proof or offer
    # an equivalent.
    System("IronRSL", 833+2941, 39253-2937),
    System("IronKV", 833+1340, 39253-7535),
    System("Ironclad DiffPriv", 6971-(81+232+140), 33203-(193+653+307)),
    System("Ironclad Notary", 6971-(81+232+586), 33203-(193+653+1613)),
    System("Yggdrasil", 1500+1500, 5),  # Fig 5; no "proof" in pushbutton, sorta. Count the invariants?
    System("Hyperkernel", 7419, 197+804+263),  # Fig 8; proof as {rep inv + state mach inv + decl spec}.
]

xs = []
ys = []
for system in systems:
    print("%-30s %-6s %-6s %3.1f" % (system.name, system.impl, system.proof, system.proof*1.0/system.impl))
    x = system.proof/1000.
    y = system.impl/1000.
    xs.append(x)
    ys.append(y)
    plt.text(x, y,
            " " + system.name + " ",
            verticalalignment="center",
            fontweight="bold" if system.name=="veribetrfs" else "roman",
            horizontalalignment="right" if system.name=="veribetrfs" else "left",
            )
plt.plot(xs, ys, "*")
plt.xlabel("⟵better        proof kLoC")
plt.ylabel("impl kLoC        better ⟶")
plt.xlim(0, plt.xlim()[1])
plt.ylim(0, plt.ylim()[1])
#plt.savefig("proof-to-code.svg")
plt.savefig("proof-to-code.png", dpi=250)
