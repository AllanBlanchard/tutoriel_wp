TOPLEVEL_PATH=$(shell which frama-c)
ifeq (, $(TOPLEVEL_PATH))
  $(error "No frama-c in PATH, it is required for tests")
endif
FRAMAC_SHARE=$(shell frama-c -print-share-path)
FRAMAC_LIB=$(shell frama-c -print-lib-path)
FRAMAC_PLUGIN=$(shell frama-c -print-plugin-path)

ifeq (, $(shell which ptests.opt))
  $(error "No ptests.opt in PATH, it is required for tests")
endif

ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))
TESTS_DIR:=$(ROOT_DIR)/tests
CACHE_DIR=$(TESTS_DIR)/cache

PTESTS_CONFIG_FILE=$(TESTS_DIR)/ptests_config

SUITES= \
  acsl-properties/lemmas \
  acsl-properties/predicates \
  acsl-properties/functions \
  proof-methodologies/triggering-lemmas \
  proof-methodologies/lemma-functions \
  proof-methodologies/minimal-contracts \
  statements/loops-examples \
  statements/loops \
  statements/function-calls \
  acsl-logic-definitions/inductive \
  acsl-logic-definitions/ghost-code \
  acsl-logic-definitions/axiomatic \
  program-proof-and-our-tool/frama-c \
  function-contract/contract \
  function-contract/well-specified \
  function-contract/modularity \
  function-contract/behaviors

all: $(TESTS_DIR) $(PTESTS_CONFIG_FILE)
	FRAMAC_WP_CACHEDIR=$(CACHE_DIR) ptests.opt $(TESTS_DIR)

$(PTESTS_CONFIG_FILE): $(TESTS_DIR)
	echo "DEFAULT_SUITES=$(SUITES)" > $(PTESTS_CONFIG_FILE)
	echo "TOPLEVEL_PATH=$(TOPLEVEL_PATH)" >> $(PTESTS_CONFIG_FILE)
	echo "FRAMAC_SHARE=$(FRAMAC_SHARE)" >> $(PTESTS_CONFIG_FILE)
	echo "FRAMAC_LIB=$(FRAMAC_LIB)" >> $(PTESTS_CONFIG_FILE)
	echo "FRAMAC_PLUGIN=$(FRAMAC_PLUGIN)" >> $(PTESTS_CONFIG_FILE)
	echo "OCAMLFIND_IGNORE_DUPS_IN=$(FRAMAC_PLUGIN)" >> $(PTESTS_CONFIG_FILE)
	echo "OCAMLRUNPARAM=" >> $(PTESTS_CONFIG_FILE)

$(TESTS_DIR):
	ln -s $(ROOT_DIR) $(TESTS_DIR)
