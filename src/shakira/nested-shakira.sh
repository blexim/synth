#!/bin/bash

basedir="`dirname $0`"
kalashnikovdir="$basedir/../kalashnikov/interpreter/"

cbmc -DWIDTH=5 -DVERIF -I $basedir -I $kalashnikovdir $basedir/util.c $basedir/abstract_transformers.c $basedir/nested-shakira.c $*
