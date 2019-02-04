import read, copy
from util import *
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
            fact_rule (Fact|Rule) - the fact or rule to be added
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

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here

        if isinstance(fact_or_rule, Fact):
            # First check to see if this fact exists and is unsupported. If it is, proceed with removal
            if fact_or_rule in self.facts:
                # Get the index of this fact
                ind = self.facts.index(fact_or_rule)

                the_fact_or_rule = self.facts[ind]

                if len(the_fact_or_rule.supported_by) > 0:
                    the_fact_or_rule.asserted = False
                else:
                    # Remove everything that this fact supports IF it was supported only by this fact
                    for f in the_fact_or_rule.supports_facts:
                        f_ind = self.facts.index(f)

                        if len(self.facts[f_ind].supported_by) == 1:
                            self.facts[f_ind].supported_by.pop()

                            if not self.facts[f_ind].asserted:
                                self.kb_retract(self.facts[f_ind])
                        elif len(self.facts[f_ind].supported_by) > 1:
                            # The fact I support is also supported by other things, so it can't be removed
                            # However, we need to update the supported by list to remove this fact
                            for i in self.facts[f_ind].supported_by:
                                i_ind = self.facts[f_ind].supported_by.index(i)

                                if (i[0] == the_fact_or_rule) or (i[1] == the_fact_or_rule):
                                    self.facts[f_ind].supported_by.pop(i_ind)

                    for r in the_fact_or_rule.supports_rules:
                        r_ind = self.rules.index(r)

                        if len(self.rules[r_ind].supported_by) == 1:
                            self.rules[r_ind].supported_by.pop()

                            if not self.rules[r_ind].asserted:
                                self.kb_retract(self.rules[r_ind])
                        elif len(self.rules[r_ind].supported_by) > 1:
                            # The rule I support is also supported by other things, so it can't be removed
                            # However, we need to update the supported by list to remove this rule
                            for i in self.rules[r_ind].supported_by:
                                i_ind = self.rules[r_ind].supported_by.index(i)
                                if (i[0] == the_fact_or_rule) or (i[1] == the_fact_or_rule):
                                    self.rules[r_ind].supported_by.pop(i_ind)

                    self.facts.pop(ind)

        if isinstance(fact_or_rule, Rule):
            # First check to see if this rule exists
            if (fact_or_rule in self.rules):
                # Get the index of this rule
                ind = self.rules.index(fact_or_rule)

                the_fact_or_rule = self.rules[ind]

                # If the rule is asserted, we never retract, so only proceed if it's not asserted
                if not the_fact_or_rule.asserted:
                    # Check to see if the rule has lost support. Only proceed if so
                    if len(the_fact_or_rule.supported_by) == 0:

                        # Remove everything that this rule supports IF it was supported only by this rule
                        for f in the_fact_or_rule.supports_facts:
                            f_ind = self.facts.index(f)

                            if len(self.facts[f_ind].supported_by) == 1:
                                self.facts[f_ind].supported_by.pop()

                                if not self.facts[f_ind].asserted:
                                    self.kb_retract(self.facts[f_ind])
                            elif len(self.facts[f_ind].supported_by) > 1:
                                # The fact I support is also supported by other things, so it can't be removed
                                # However, we need to update the supported by list to remove this fact
                                for i in self.facts[f_ind].supported_by:
                                    i_ind = self.facts[f_ind].supported_by.index(i)
                                    if (i[0] == the_fact_or_rule) or (i[1] == the_fact_or_rule):
                                        self.facts[f_ind].supported_by.pop(i_ind)

                        for r in the_fact_or_rule.supports_rules:
                            r_ind = the_fact_or_rule.supports_rules.index(r)

                            if len(self.rules[r_ind].supported_by) == 1:
                                self.rules[r_ind].supported_by.pop()

                                if not self.rules[r_ind].asserted:
                                    self.kb_retract(self.rules[r_ind])
                            elif len(self.rules[r_ind].supported_by) > 1:
                                # The rule I support is also supported by other things, so it can't be removed
                                # However, we need to update the supported by list to remove this rule
                                for i in self.rules[r_ind].supported_by:
                                    i_ind = self.rules[r_ind].supported_by.index(i)
                                    if (i[0] == the_fact_or_rule) or (i[1] == the_fact_or_rule):
                                        self.rules[r_ind].supported_by.pop(i_ind)

                        # After clearing all dependent facts and rules, remove this rule
                        self.rules.pop(ind)


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

        # First check to see if there is a matching set of bindings
        bindings = match(fact.statement, rule.lhs[0])

        # If some bindings were returned, process
        if bindings:
            # The rule could have multiple statements. If it has just one, and we have a match,
            # the resulting item must be a fact. Otherwise, we have a shorter rule
            if len(rule.lhs) == 1:
                # Instantiate the rule with the binding and insert into KB
                inferred_fact = lc.Fact(instantiate(rule.rhs, bindings), [[fact, rule]])
                kb.kb_assert(inferred_fact)
                fact.supports_facts.append(inferred_fact)
                rule.supports_facts.append(inferred_fact)
            else:
                # Create a new rule that eliminate the first statement in LHS
                new_lhs = []
                for i in range(1, len(rule.lhs)):
                    new_lhs.append(instantiate(rule.lhs[i], bindings))

                inferred_rule = lc.Rule([new_lhs, instantiate(rule.rhs, bindings)], [[fact, rule]])

                kb.kb_assert(inferred_rule)
                fact.supports_rules.append(inferred_rule)
                rule.supports_rules.append(inferred_rule)
