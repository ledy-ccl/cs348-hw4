import read, copy
from util import *
from util import match
from util import instantiate
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact or Rule) - Fact or Rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []
        
    #   help functions   
    def kb_contains(self, fact_rule):
        """Check if a fact or rule exists in the KB.

        Args:
            fact_rule (Fact or Rule): The Fact or Rule to check.

        Returns:
            bool: True if the fact or rule exists, False otherwise.
        """
        if isinstance(fact_rule, Fact):
            return fact_rule in self.facts
        elif isinstance(fact_rule, Rule):
            return fact_rule in self.rules
        return False
    def _kb_remove(self, fact_rule):
        """Remove a fact or rule from the KB.

        Args:
            fact_rule (Fact or Rule): The Fact or Rule to be removed.

        Returns:
            None
        """
        if isinstance(fact_rule, Fact):
            if fact_rule in self.facts:
                self.facts.remove(fact_rule)
        elif isinstance(fact_rule, Rule):
            if fact_rule in self.rules:
                self.rules.remove(fact_rule)

    def kb_retract(self, fact_rule):
        """Retract a fact or a rule from the KB

        Args:
            fact_rule (Fact or Rule) - Fact or Rule to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_rule])
        ####################################################
        # Student code goes here
        if isinstance(fact_rule, Fact):
            kb_fact = self._get_fact(fact_rule)
            if kb_fact:
                if kb_fact.asserted:
                    kb_fact.asserted = False
                if not kb_fact.supported_by:
                    self._kb_remove(kb_fact)
                    for supported_fact in kb_fact.supports_facts:
                        supported_fact.supported_by = [pair for pair in supported_fact.supported_by if pair[0] != kb_fact]
                        if not supported_fact.supported_by and not supported_fact.asserted:
                            self.kb_retract(supported_fact)
                    for supported_rule in kb_fact.supports_rules:
                        supported_rule.supported_by = [pair for pair in supported_rule.supported_by if pair[0] != kb_fact]
                        if not supported_rule.supported_by and not supported_rule.asserted:
                            self.kb_retract(supported_rule)

        elif isinstance(fact_rule, Rule):
            kb_rule = self._get_rule(fact_rule)
            if kb_rule:
                if kb_rule.asserted:
                    kb_rule.asserted = False
                if not kb_rule.supported_by:
                    self._kb_remove(kb_rule)
                    for supported_fact in kb_rule.supports_facts:
                        supported_fact.supported_by = [pair for pair in supported_fact.supported_by if pair[1] != kb_rule]
                        if not supported_fact.supported_by and not supported_fact.asserted:
                            self.kb_retract(supported_fact)
                    for supported_rule in kb_rule.supports_rules:
                        supported_rule.supported_by = [pair for pair in supported_rule.supported_by if pair[1] != kb_rule]
                        if not supported_rule.supported_by and not supported_rule.asserted:
                            self.kb_retract(supported_rule)
    

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        bindings = match(fact.statement, rule.lhs[0])
        if bindings:
            if len(rule.lhs) == 1:  # Infer a new fact
                new_fact = Fact(instantiate(rule.rhs, bindings), supported_by=[[fact, rule]])
                fact.supports_facts.append(new_fact)
                rule.supports_facts.append(new_fact)
                kb.kb_assert(new_fact)
            else:  # Infer a new curried rule
                new_lhs = [instantiate(statement, bindings) for statement in rule.lhs[1:]]
                new_rhs = instantiate(rule.rhs, bindings)
                new_rule = Rule([new_lhs, new_rhs], supported_by=[[fact, rule]])
                fact.supports_rules.append(new_rule)
                rule.supports_rules.append(new_rule)
                kb.kb_assert(new_rule)
