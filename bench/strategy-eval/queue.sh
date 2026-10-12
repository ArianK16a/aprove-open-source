#!/bin/bash
# usage: queue.sh SET VARIANT...
cd "$(dirname "$0")"
set_=$1; shift
for v in "$@"; do ./runvariant.sh "$v" "$set_" 30; done
