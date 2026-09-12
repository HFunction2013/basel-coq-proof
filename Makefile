# Makefile for basel-coq
# 使用方法：
#   make         # 生成 Coq Makefile 并编译
#   make clean   # 清理编译产物
#
# 前提：已安装 Coq（coqc, coq_makefile 在 PATH 中）
# 安装方法：
#   - opam: opam install coq
#   - apt:  sudo apt install coq
#   - Nix:  nix-shell -p coq

COQMAKEFILE ?= CoqMakefile

.PHONY: all clean configure

all: configure
	$(MAKE) -f $(COQMAKEFILE) all

configure:
	coq_makefile -f _CoqProject -o $(COQMAKEFILE)

clean:
	if [ -f $(COQMAKEFILE) ]; then $(MAKE) -f $(COQMAKEFILE) clean; fi
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf
