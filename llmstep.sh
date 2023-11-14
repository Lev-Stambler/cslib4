#!/bin/sh
source $HOME/anaconda3/bin/activate base
cd lake-packages/llmstep
python3 python/server_vllm.py
# Not enough memory :(
# Ooooh talk to Matt?
# python3 python/server_llemma.py