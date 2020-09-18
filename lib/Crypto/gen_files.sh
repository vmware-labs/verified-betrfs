#!/bin/bash
python3 gen2.py main > CRC32Lut.i.dfy
python3 gen2.py unrolling > CRC32LutBitUnrolling.i.dfy
python3 gen.py > CRC32LutPowers.i.dfy
