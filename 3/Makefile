-include coq.depends
all: TAGS src tactic test proof TODOS

SRCFILES=FormalSyntax.vo GetLemmasRelation.vo ListLemmas.vo AlphaConversion.vo DynamicSemanticsTypeSubstitution.vo DynamicSemanticsHeapObjects.vo DynamicSemantics.vo StaticSemanticsKindingAndContextWellFormedness.vo StaticSemanticsTypingHeapObjects.vo StaticSemantics.vo Tacticals.vo TacticNotations.vo TypeSafety.vo

TESTFILES=TestUtilities.vo FormalSyntaxTest.vo DynamicSemanticsHeapObjectsTest.vo DynamicSemanticsTypeSubstitutionTest.vo DynamicSemanticsTest.vo StaticSemanticsTest.vo StaticSemanticsKindingAndContextWellFormednessTest.vo StaticSemanticsTypingHeapObjectsTest.vo MutualRecursionProof.vo KindingTest.vo

PROOFFILES=TypeSafetyProof.vo ContextWeakeningProof.vo TermWeakeningProof.vo HeapWeakeningProof.vo SubstitutionsProof.vo TypingWellFormednessProof.vo ReturnPreservationProof.vo CannonicalFormsProof.vo PathExtensionProof.vo HeapObjectSafetyProof.vo TermPreservationProof.vo TermProgressProof.vo

TACTICFILES=CpdtTactics.vo Case.vo

%.vo: %.v 
	coqc $<

src:  TAGS depends $(SRCFILES)

tactic: TAGS src $(TACTICFILES)

test: TAGS depends src $(TESTFILES)

proof: TAGS depends src $(PROOFFILES)

clean:
	rm -f *.vo
	rm -f *~ 
	rm -f *.glob
	rm -f TAGS

tar:
	tar zcvf backup.tar.gz *.v Makefile

TAGS:  
	~/bin/coqtags *.v

count: 
	echo "Source "
	ls -1 *.v | grep -vi Test | grep -v Dead | grep -v Proof | grep -v Subset | grep -v Cpdt | xargs wc -l 
	echo "Test "
	ls -1 *.v | grep -i Test | xargs wc -l 
	echo "TypeSafety "
	ls -1 *.v | grep -i Proof | grep -v Subset | xargs wc -l 

depends: 
	coqdep -I . *.v > coq.depends 

TODOS:
	grep admit *.v | grep -v Proof | wc -l
	grep Admitted *.v | grep -v Proof | wc -l
	grep Admitted *.v | grep Proof | wc -l
	grep TODO TODO *.v | wc -l
	grep '?' *.v | grep -v Tacticals | wc -l
	grep -e Admitted -e TODO -e '?' *.v | wc -l

BUGS:
	grep Bug *.v 
	grep Bug *.v | wc -l
	grep 'Test Bug' *.v | wc -l
	grep 'Dan Bug' *.v | wc -l

ttpbis:
	echo "To Prove"
	grep -e Lemma -e Theorem *Proof.v | grep -v Subset | wc -l
	echo "Proven".
	grep -e Qed *Proof.v | grep -v Subset | wc -l
	echo "Cases missing".
	grep admit *.v | grep Proof | wc -l


dan: 
	echo "Ask Dan's"
	grep -e Dan *.v | grep -v formal | wc -l

