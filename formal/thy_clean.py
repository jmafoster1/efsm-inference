#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import re
import os
import sys


def line_of_char(text, c):
    return text[:c].count("\n") + 1


filename = sys.argv[1]
if filename.endswith(".thy"):

    with open(filename) as file:
        text = file.read()

    named_lemmas = {(line_of_char(text, m.start()), m.group(2))
                    for m in re.finditer("lemma(s?) (\w*)(:| |=)", text)}
    names = {m[1] for m in named_lemmas}

    used = set()
    for root, dirs, files in os.walk("."):
        for f in files:
            if f.endswith(".thy"):
                filepath = os.path.join(root, f)
                with open(filepath) as search_file:
                    words = set(re.findall("(?<!lemma )\w+",
                                           search_file.read()))
                    named_used = names.intersection(words)
                    used = used.union(named_used)

    print("There are", len(named_lemmas), "named lemmas in", filename,
          "of which", len(names.difference(used)), "are unused:")

    unused = list({m for m in named_lemmas if m[1] not in used})
    for line_no, name in sorted(unused):
        print(" ", line_no, name)
else:
    print("Invalid theory file", sys.argv[1])
