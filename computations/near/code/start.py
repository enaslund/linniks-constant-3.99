"""Shared active arithmetic and portable result paths."""
import os, sys, json, gzip
from pathlib import Path
if not __debug__:
    raise RuntimeError('Verification requires Python assertions enabled; do not use -O')
os.environ['OPENBLAS_NUM_THREADS'] = '1'
os.environ['OMP_NUM_THREADS'] = '1'
PACKAGE = Path(__file__).resolve().parents[1]
ROOT = PACKAGE.parent / 'core'
sys.path.insert(0, str(ROOT / 'code'))
from endgame import *
from optimize_near import trans, norm0
from certificate_io import load_data, check_input, input_summary, parameters_of
import numpy as np
