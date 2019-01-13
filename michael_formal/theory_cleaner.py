#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sun Jan 13 11:39:13 2019

@author: michael
"""

import re
import os

root = '/home/michael/Documents/elixir/athena2/michael_formal/'
lemma_re = re.compile('\s*(have|lemma) ((\w)*?):')
apply_re = re.compile('\s*(apply|by) \((simp|metis|simp_all) (add|only): ((\w| )*)\s*\)\s*')
using_re = re.compile('\s*using ((\w| )*)\s*')
lemmas_re = re.compile('\s*lemmas \w* = ((\w| )*)')

for root, dirs, files in os.walk(root):
    for file in files:
        if file.endswith("DM_Inference.thy"):
            lemmas_named = set()
            lemmas_used = set()
            filepath = os.path.join(root, file)
            print(file)
            with open(filepath) as f:
                for line in f:
                    named_lemma = lemma_re.match(line)
                    simps = apply_re.match(line)
                    using = using_re.match(line)
                    lemmas = lemmas_re.match(line)
                    if named_lemma:
                        lemmas_named.add(named_lemma.group(2))
#                        print(named_lemma.group(1))
                    if simps:
#                        print(simps.group(4).split(' '))
                        lemmas_used = lemmas_used.union(set(simps.group(4).split(' ')))
                    if using:
#                        print(using.group(1).split(' '))
                        lemmas_used = lemmas_used.union(set(using.group(1).split(' ')))
                    if lemmas:
#                        print(lemmas.group(1).split(' '))
                        lemmas_used = lemmas_used.union(set(lemmas.group(1).split(' ')))

            print()
            print(len(lemmas_named), sorted(list(lemmas_named)))
            print()
            print(len(lemmas_used.intersection(lemmas_named)), sorted(list(lemmas_used.intersection(lemmas_named))))
            print()
            print(len(lemmas_named.difference(lemmas_used)), sorted(list(lemmas_named.difference(lemmas_used))))
            print('\n')
