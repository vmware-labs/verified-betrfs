rm -rf boogie-partners
git clone https://github.com/boogie-org/boogie-partners.git
(cd boogie-partners/CocoR/Modified/; mv parser.frame Parser.frame; mv scanner.frame Scanner.frame;)
#mono ../../third_party/Coco/bin/Coco.exe Dafny.atg  -namespace Microsoft.Dafny -frames ../../third_party/Coco/src

# Use the Coco that came with Dafny, duh!
(cd ../../third_party/Coco/src; ln -s parser.frame Parser.frame; ln -s scanner.frame Scanner.frame)
mono ../../third_party/Coco/bin/Coco.exe Dafny.atg  -namespace Microsoft.Dafny -frames ../../third_party/Coco/src
