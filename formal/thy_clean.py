#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import re
import os
import sys

def line_of_char(text, c):
    return text[:c].count("\n") + 1


named_lemma = re.compile("lemma(s?) (\w*)(:| |=)")

filename = sys.argv[1]
if filename.endswith(".thy"):
    with open(filename) as file:
        text = file.read()

    count = 0
    named_lemmas = set()
    for m in named_lemma.finditer(text):
        count += 1
        named_lemmas.add((line_of_char(text, m.start()), m.group(2)))

    used = set()
    for root, dirs, files in os.walk("."):
        for f in files:
            if f.endswith(".thy"):
                filepath = os.path.join(root, f)
                with open(filepath) as search_file:
                    for line in search_file:
                        for line_no, name in named_lemmas.difference(used):
                            if name in line and "lemma " not in line:
                                used.add((line_no, name))
    print("There are", count, "named lemmas in", filename, "of which", len(named_lemmas.difference(used)), "are unused")

    for line_no, name in sorted(list(named_lemmas.difference(used))):
        print(line_no, name)
else:
    print("Invalid theory file", sys.argv[1])
