#!/usr/bin/env python3
import subprocess
import time
import numpy as np

"""
# Before changes
/home/jonh/verus/source/target-verus/release/verus --time --expand-errors --multiple-errors 500 src/bundle.rs
verification results:: verified: 266 errors: 0

find src -name \*.rs | xargs grep '\<spec\> ' --color | wc -l
421

# With changes
find src -name \*.rs | xargs sed -i 's/\<spec\> /spec(checked) /'

/home/jonh/verus/source/target-verus/release/verus --time --expand-errors --multiple-errors 500 src/bundle.rs
error: aborting due to 5 previous errors; 84 warnings emitted
verification results:: verified: 263 errors: 3

[ ] Why did it abort? I gave it a budget of 500.
[ ] There are 84 failures. Happy to fix them, but they may be inflating the output a bit.
[ ] Got two copies of "note: function body check has been running for 2 seconds"

unchecked: μ=7.84 σ=0.06
checked: μ=13.69 σ=0.14
cost: 5.9s 74.7%

"""

def sample():
    times = []
    for i in range(10):
        start = time.time()
        subprocess.call(["/home/jonh/verus/source/target-verus/release/verus", "--time", "--expand-errors", "--multiple-errors", "5", "src/bundle.rs"],
                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        end = time.time()
        elapsed = end-start
        times.append(elapsed)
        print(elapsed)
    print(times)

def summarize():
    #    unchecked_results = [7.823099851608276, 7.838244676589966, 7.847527027130127, 7.8952460289001465, 7.736751079559326, 7.819883108139038, 7.779019355773926, 7.8980066776275635, 7.960920333862305, 7.782015085220337]

    #checked_results = [13.677567720413208, 13.758004903793335, 13.611055135726929, 13.632875204086304, 13.718096733093262, 13.662260293960571, 13.608689546585083, 13.519087791442871, 13.661466836929321, 14.057171106338501]

    unchecked_results = [5.367572784423828, 5.808064699172974, 5.840511083602905, 5.749913930892944, 5.860361099243164, 5.876439809799194, 5.686094284057617, 5.676607608795166, 5.684131860733032, 5.803192377090454]
    checked_results = [5.1796863079071045, 5.636549472808838, 5.658161163330078, 5.760870933532715, 5.737208604812622, 5.8875837326049805, 5.987775802612305, 5.858651399612427, 5.81020450592041, 5.834321737289429]

    for vn in ["unchecked", "checked"]:
        expr = vn+"_results"
        data = eval(expr)
        print(f"{vn}: μ={np.mean(data):0.2f} σ={np.std(data):0.2f}")

    delta = np.mean(checked_results) - np.mean(unchecked_results)
    print(f"cost: {delta:0.1f}s {delta/np.mean(unchecked_results)*100:0.1f}%")

#sample()
summarize()
