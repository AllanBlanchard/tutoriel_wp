TOPLEVEL_PATH=$(shell which frama-c)
ifeq (, $(TOPLEVEL_PATH))
  $(error "No frama-c in PATH, it is required for tests")
endif
FRAMAC_SHARE=$(shell frama-c -print-share-path)
FRAMAC_LIB=$(shell frama-c -print-lib-path)
FRAMAC_PLUGIN=$(shell frama-c -print-plugin-path)

ifeq (, $(shell which frama-c-ptests))
  $(error "No frama-c-ptests in PATH, it is required for tests")
endif

ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))
LINK:=$(ROOT_DIR)/tests
CACHE_DIR=$(ROOT_DIR)/cache

PTESTS_CONFIG_FILE=$(LINK)/ptests_config

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
  statements/basic \
  acsl-logic-definitions/inductive \
  acsl-logic-definitions/ghost-code \
  acsl-logic-definitions/axiomatic \
  program-proof-and-our-tool/frama-c \
  function-contract/contract \
  function-contract/well-specified \
  function-contract/modularity \
  function-contract/behaviors

all: prepare-tests run-tests

prepare-tests: $(LINK) $(PTESTS_CONFIG_FILE)
	frama-c-ptests $(LINK)
	rm $(LINK)

create-oracles: $(LINK) $(PTESTS_CONFIG_FILE)
	frama-c-ptests -create-missing-oracles $(LINK)
	rm $(LINK)

clean-oracles: $(LINK) $(PTESTS_CONFIG_FILE)
	frama-c-ptests -remove-empty-oracles $(LINK)
	rm $(LINK)

run-tests:
	FRAMAC_WP_CACHEDIR=$(CACHE_DIR) dune build @ptests

$(PTESTS_CONFIG_FILE): $(LINK)
	echo "DEFAULT_SUITES=$(SUITES)" > $(PTESTS_CONFIG_FILE)

$(LINK):
	ln -s $(ROOT_DIR) $(LINK)
