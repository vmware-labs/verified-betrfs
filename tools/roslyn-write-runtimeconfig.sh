#! /bin/bash

RUNTIME=`dotnet --list-runtimes | grep 'Microsoft.NETCore.App' | head -n 1 | sed 's/.* \(.*\) .*/\1/'`

echo dotnet core runtime $RUNTIME >&2

echo "{\"runtimeOptions\": { \"framework\": { \"name\": \"Microsoft.NETCore.App\", \"version\": \"$RUNTIME\" } } }"
