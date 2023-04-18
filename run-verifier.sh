#!/bin/bash

set -e
make concurrency-status -j4
make build/concurrency/SeagullBundle.i.lcreport
