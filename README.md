# TRX - Tree Regular Expressions for Racket

**Author:** Joseph Irwin

## Overview

This is a library for matching trees in Racket, based on a paper by Ilya Bagrak
and Olin Shivers:

    Ilya Bagrak and Olin Shivers. [trx: Regular-tree expressions, now in Scheme](http://repository.readscheme.org/ftp/papers/sw2004/bagrak.pdf). In
        *Proceedings of the Fifth Workshop on Scheme and Functional Programming*,
        pages 21-32, Snowbird, Utah, September 2004.

According to the paper, the code should be included in scsh, but it doesn't seem
to exist anywhere on the Internet, so I decided to reimplement it myself (in
Racket). My (admittedly un-expert) impression is that macros in Racket are much
easier to write than the low-level macros in scheme48.

## Status

Missing:

- `let` and `letrec` forms
- submatches

Other than the above, the basic functionality is there, including recursive patterns.

## How to Use

I wouldn't. But if you really must, read the paper and try out some of the examples.

## Copying

[![CC0](http://i.creativecommons.org/p/zero/1.0/88x31.png)](http://creativecommons.org/publicdomain/zero/1.0/)

To the extent possible under law, the author(s) have dedicated all copyright
and related and neighboring rights to this software to the public domain
worldwide. This software is distributed without any warranty.

You should have received a copy of the CC0 Public Domain Dedication along with
this software. If not, see <http://creativecommons.org/publicdomain/zero/1.0/>.
