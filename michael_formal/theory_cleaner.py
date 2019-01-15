#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sun Jan 13 14:20:44 2019

@author: michael
"""

import re
import os

root = '/home/michael/Documents/elixir/athena2/michael_formal/'

for root, dirs, files in os.walk(root):
    for file in files:
        if file.endswith(".thy"):
            lemmas_named = set()
            lemmas_used = set()
            duplicate_names = set()
            filepath = os.path.join(root, file)
            with open(filepath) as f:
                theory = f.read()
                named_lemmas = re.finditer('\s*(have|lemma) ((\w)*?):', theory)
                applies = re.finditer('\s*(apply|by) \((simp|metis|simp_all) (add|only): ((\w|\.|\s*)*)\s*\)\s*', theory)
                usings = re.finditer('\s*using ((\w| )*)\s*', theory)
                lemmas = re.finditer('\s*lemmas \w* = ((\w| )*)', theory)
            for lemma in named_lemmas:
#                print(lemma.group(2))
                if lemma.group(2) in lemmas_named:
                    duplicate_names.add(lemma.group(2))
                else:
                    lemmas_named.add(lemma.group(2))
            for apply in applies:
#                print(apply.group(4).split(' '))
                lemmas_used = lemmas_used.union(set([x.strip() for x in apply.group(4).split(' ')]))
            for using in usings:
#                print(using.group(1).split(' '))
                lemmas_used = lemmas_used.union(set([x.strip() for x in using.group(1).split(' ')]))
            for lemma in lemmas:
#                print(lemma.group(1).split(' '))
                lemmas_used = lemmas_used.union([x.strip() for x in set(lemma.group(1).split(' '))])

            if len(lemmas_named.difference(lemmas_used)) > 0 or len(duplicate_names) > 0:
                print(file)
    #            print(len(lemmas_named), sorted(list(lemmas_named)))
    #            print()
    #            print(len(lemmas_used.intersection(lemmas_named)), sorted(list(lemmas_used.intersection(lemmas_named))))
    #            print()
                print(len(lemmas_named.difference(lemmas_used)), sorted(list(lemmas_named.difference(lemmas_used))))
                print(sorted(list(duplicate_names)))
                print('\n')
