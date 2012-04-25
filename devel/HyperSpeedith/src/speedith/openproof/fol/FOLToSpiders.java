/*
 *   Project: HyperSpeedith
 * 
 * File name: FOLToSpiders.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2012 Matej Urbas
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package speedith.openproof.fol;

import java.util.*;
import openproof.fol.representation.*;
import speedith.core.lang.*;
import speedith.core.util.Sets;

/**
 * Converts an Openproof {@link OPFormula FOL formula} into a {@link SpiderDiagram spider diagram}.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class FOLToSpiders {

	//<editor-fold defaultstate="collapsed" desc="Private Fields">
	private static final int MORE_THAN_ONE_SPIDER_MENTIONED = -1;
	private static final int NON_SPIDER_MENTIONED = -2;
	private static final int NON_UNARY_PREDICATE_MENTIONED = -3;
	private static final int UNKNOWN_TERM_MENTIONED = -4;
	//</editor-fold>

	//<editor-fold defaultstate="collapsed" desc="Public Methods">
	/**
	 * Takes an Openproof {@link OPFormula FOL formula} and converts it into an
	 * equivalent spider diagram.
	 *
	 * @param formula an Openproof FOL formula. <p>This argument must not be {@code null},
	 * an {@link IllegalArgumentException} will be thrown if it is.</p>
	 * @return the converted spider diagram
	 * @throws ConversionException this exception is thrown if the conversion
	 * from the given FOL formula fails for reasons relating to unknown formula
	 * format or presence of language elements that cannot be mapped to spider
	 * diagrams.
	 */
	public static SpiderDiagram convert(OPFormula formula) throws ConversionException {
		if (formula == null) {
			throw new IllegalArgumentException(speedith.core.i18n.Translations.i18n("GERR_NULL_ARGUMENT", "formula"));
		}

		return snf2sd(formula);
	}
	//</editor-fold>

	// <editor-fold defaultstate="collapsed" desc="Constructor">
	private FOLToSpiders() {
	}
	// </editor-fold>

	// <editor-fold defaultstate="collapsed" desc="Private Helper Methods">
	/**
	 * This method expects a general Openproof first-order formula, and returns
	 * a spider diagram.
	 *
	 * This is a syntactical translation method. It does not transform the
	 * formula into any other form.
	 *
	 * @param formula
	 * @return
	 * @throws ConversionException
	 */
	private static SpiderDiagram snf2sd(OPFormula formula) throws ConversionException {
		if (formula instanceof OPDisjunction) {
			return nary2csd((NAryFormula) formula, Operator.Disjunction);
		} else if (formula instanceof OPConjunction) {
			return nary2csd((NAryFormula) formula, Operator.Conjunction);
		} else if (formula instanceof OPImplication) {
			return binary2csd((BinaryFormula) formula, Operator.Implication);
		} else if (formula instanceof OPBiconditional) {
			return binary2csd((BinaryFormula) formula, Operator.Equivalence);
		} else if (formula instanceof OPNegation) {
			return unary2csd((UnaryFormula) formula, Operator.Negation);
		} else if (formula instanceof OPExistential) {
			return existential2psd((OPExistential) formula, Operator.Negation);
		} else {
			throw new ConversionException(speedith.openproof.i18n.Translations.i18n("FOL2SD_UNKNOWN_FORMULA", formula.toString()));
		}
	}

	private static SpiderDiagram nary2csd(NAryFormula nAryFormula, Operator operator) throws ConversionException {
		final OPFormulaList juncts = nAryFormula.getJuncts();
		SpiderDiagram sd = snf2sd(juncts.formulaAt(0));
		for (int i = 1; i < juncts.count(); i++) {
			sd = SpiderDiagrams.createCompoundSD(operator, sd, snf2sd(juncts.formulaAt(i)));
		}
		return sd;
	}

	private static CompoundSpiderDiagram binary2csd(BinaryFormula binaryFormula, Operator operator) throws ConversionException {
		return SpiderDiagrams.createCompoundSD(operator, snf2sd(binaryFormula.getLeft()), snf2sd(binaryFormula.getRight()));
	}

	private static CompoundSpiderDiagram unary2csd(UnaryFormula unaryFormula, Operator operator) throws ConversionException {
		throw new ConversionException(speedith.openproof.i18n.Translations.i18n("FOL2SD_NOT_IMPLEMENTED_YET", unaryFormula.toUnicode()));
	}

	private static SpiderDiagram existential2psd(OPExistential formula, Operator operator) throws ConversionException {
		// First get all the nested existentially quantified variables.
		TreeSet<String> spiders = new TreeSet<String>();

		// This code extracts all the spider names from the existentially
		// quantified variables.
		OPFormula innerFormula = null;
		do {
			spiders.add(formula.getBoundVar().toString());
			if (formula.getMatrixFormula() instanceof OPExistential) {
				formula = (OPExistential) formula.getMatrixFormula();
			} else {
				innerFormula = formula.getMatrixFormula();
			}
		} while (innerFormula == null);
		// We have a list of all spiders. Get a sorted array out of it:
		String[] spidersArr = spiders.toArray(new String[0]);

		// The inner formula should be a conjunction of terms. Let's extract
		// all the conjuncts into a list:
		ArrayList<OPFormula> conjuncts = new ArrayList<OPFormula>();
		extractConjuncts(innerFormula, conjuncts);

		// Okay, we have all the spiders now. Also, we have the inner term,
		// which should contain the following elements of the primary spider
		// diagram:
		//		-	distinctive spiders declaration
		//		-	spider habitats
		//		-	shaded zones

		// SPIDER STUFF:
		// Check that all spider inequalities are present. Also remove the
		// conjuncts that contain these inequalities.
		checkSpiderInequalities(spiders, conjuncts, spidersArr);

		// CONTOUR STUFF:
		// This set contains all the contours thar are present in this primary spider
		// diagram.
		TreeSet<String> contours = new TreeSet<String>();
		// Extract all mentioned contour names:
		for (OPFormula conjunct : conjuncts) {
			extractContourNames(conjunct, contours, spidersArr);
		}
		String[] contoursArr = contours.toArray(new String[0]);

		// HABITATS STUFF:
		// Now get the habitats:
		TreeMap<String, Region> habitats = new TreeMap<String, Region>();
		extractHabitats(conjuncts, habitats, contoursArr, spidersArr);

		// SHADED ZONES STUFF:
		// TODO: Implement parsing for shaded zones.
		if (conjuncts.size() > 0) {
			throw new ConversionException(speedith.openproof.i18n.Translations.i18n("FOL2SD_UNKNOWN_FORMULAE", Sets.toString(conjuncts)));
		}

		return SpiderDiagrams.createPrimarySDNoCopy(spiders, habitats, null, null);
	}

	/**
	 * Extracts all the conjuncts (nested or not) from the inner formula. For
	 * example the formula 'A & (B & (C | D)) & (D -> E & F) & (A & B)' will
	 * thus return the list: [A, B, (C | D), D -> E & F, A, B].
	 *
	 * @param formula
	 * @param conjuncts
	 */
	private static void extractConjuncts(OPFormula formula, ArrayList<OPFormula> conjuncts) {
		if (formula instanceof OPConjunction) {
			OPFormulaList innerConjuncts = ((OPConjunction) formula).getJuncts();
			for (int i = 0; i < innerConjuncts.count(); i++) {
				extractConjuncts(innerConjuncts.formulaAt(i), conjuncts);
			}
		} else {
			conjuncts.add(formula);
		}
	}

	private static ArrayList<OPFormula> extractConjuncts(OPFormula formula) {
		ArrayList<OPFormula> conjuncts = new ArrayList<OPFormula>();
		extractConjuncts(formula, conjuncts);
		return conjuncts;
	}

	private static ArrayList<OPFormula> extractDisjuncts(OPFormula formula) {
		ArrayList<OPFormula> disjuncts = new ArrayList<OPFormula>();
		extractDisjuncts(formula, disjuncts);
		return disjuncts;
	}

	/**
	 * Extracts all the disjuncts (nested or not) from the inner formula. For
	 * further explanation see {@link FOLToSpiders#extractConjuncts(openproof.fol.representation.OPFormula, java.util.ArrayList)
	 * }.
	 *
	 * @param formula
	 * @param disjuncts
	 */
	private static void extractDisjuncts(OPFormula formula, ArrayList<OPFormula> disjuncts) {
		if (formula instanceof OPDisjunction) {
			OPFormulaList innerDisjuncts = ((OPDisjunction) formula).getJuncts();
			for (int i = 0; i < innerDisjuncts.count(); i++) {
				extractDisjuncts(innerDisjuncts.formulaAt(i), disjuncts);
			}
		} else {
			disjuncts.add(formula);
		}
	}

	/**
	 * This function checks whether all the spider inequalities are present in
	 * the primary spider diagram. It also removes all the terms that contain
	 * these inequalities from the conjuncts. It throws an exception if an
	 * unexpected conjunct is found.
	 *
	 * @param spiders
	 * @param conjuncts
	 * @param spidersArr
	 * @throws ConversionException
	 */
	private static void checkSpiderInequalities(TreeSet<String> spiders, ArrayList<OPFormula> conjuncts, String[] spidersArr) throws ConversionException {
		// This array contains flags that indicate whether an inequality
		// assertion between two spiders has been made in the formula. Thus,
		// if two spiders with indices 'i' and 'j' are found in an inequality
		// assertion (i.e. 's(i) != s(j)'), then the flag at index 'i * spiders.size() + j'
		// is set to 'true'. Note that if the same spider is declared not equal
		// to itself, then elements at indices (e.g. 'i*spiders.size() + i')
		// will be 'true'.
		boolean[] inequalities = new boolean[spiders.size() * spiders.size()];
		// Now find all the inequality terms:
		for (int i = 0; i < conjuncts.size(); i++) {
			OPFormula conjunct = conjuncts.get(i);

			// The spider inequality term must be a negation, that contains an
			// inequality of two spiders.
			if (!(conjunct instanceof OPNegation)) {
				continue;
			}
			final OPFormula negated = ((OPNegation) conjunct).getNegated();
			if (!(negated instanceof OPAtom)) {
				continue;
			}
			// Finally, do we have an inequality?
			OPAtom atom = (OPAtom) negated;
			if (!"=".equals(atom.getPredicateSymbol())) {
				continue;
			}
			// The inequality must contain two spiders:
			OPTermList arguments = atom.getArguments();
			if (arguments.count() != 2
					|| !(arguments.termAt(0) instanceof OPVariable)
					|| !(arguments.termAt(1) instanceof OPVariable)) {
				// There should be no other inequalities in the conjuncts! Throw
				// a conversion exception if one is found!
				throw new ConversionException(speedith.openproof.i18n.Translations.i18n("FOL2SD_UNKNOWN_FORMULA", conjunct.toString()));
			}
			// Now find the indices of the two spiders:
			int spIndexA = Arrays.binarySearch(spidersArr, ((OPVariable) arguments.termAt(0)).toString());
			int spIndexB = Arrays.binarySearch(spidersArr, ((OPVariable) arguments.termAt(1)).toString());
			if (spIndexA < 0 || spIndexB < 0 || spIndexA == spIndexB) {
				throw new ConversionException(speedith.openproof.i18n.Translations.i18n("FOL2SD_UNKNOWN_FORMULA", conjunct.toString()));
			}
			inequalities[Math.min(spIndexA, spIndexB) * spidersArr.length + Math.max(spIndexA, spIndexB)] = true;
			// Now remove the term from the list of terms and continue:
			conjuncts.remove(i--);
		}
		// Now check that all required inequalities are present
		for (int i = 0; i < spidersArr.length; i++) {
			for (int j = i + 1; j < spidersArr.length; j++) {
				if (!inequalities[i * spidersArr.length + j]) {
					throw new ConversionException(speedith.openproof.i18n.Translations.i18n("FOL2SD_SPIDER_INEQUALITIES_MISSING", spidersArr[i], spidersArr[j]));
				}
			}
		}
	}

	/**
	 * Extracts all predicate symbols which appear as contours in the formula. A
	 * predicate 'P' is a contour if it is of the form 'P(t)' where 't' is a
	 * spider.
	 *
	 * @param formula
	 * @param contours
	 * @param spidersArr
	 */
	private static void extractContourNames(OPFormula formula, TreeSet<String> contours, String[] spidersArr) {
		if (formula instanceof OPAtom) {
			OPAtom atom = (OPAtom) formula;
			OPTermList arguments = atom.getArguments();
			if (arguments != null
					&& arguments.count() == 1
					&& arguments.termAt(0) instanceof OPVariable
					&& Arrays.binarySearch(spidersArr, ((OPVariable) arguments.termAt(0)).toString()) >= 0) {
				contours.add(atom.getPredicateSymbol());
			}
		} else if (formula instanceof NAryFormula) {
			OPFormulaList juncts = ((NAryFormula) formula).getJuncts();
			for (int i = 0; i < juncts.count(); i++) {
				extractContourNames(juncts.formulaAt(i), contours, spidersArr);
			}
		} else if (formula instanceof BinaryFormula) {
			extractContourNames(((BinaryFormula) formula).getLeft(), contours, spidersArr);
			extractContourNames(((BinaryFormula) formula).getRight(), contours, spidersArr);
		} else if (formula instanceof UnaryFormula) {
			extractContourNames(((UnaryFormula) formula).getSubFormula(), contours, spidersArr);
		} else if (formula instanceof QuantifiedFormula) {
			extractContourNames(((QuantifiedFormula) formula).getMatrixFormula(), contours, spidersArr);
		}
	}

	private static void extractHabitats(ArrayList<OPFormula> conjuncts, TreeMap<String, Region> habitats, String[] contoursArr, String[] spidersArr) throws ConversionException {
		for (int i = 0; i < conjuncts.size(); i++) {
			int removedCount = extractHabitat(i, conjuncts, habitats, contoursArr, spidersArr);
			if (removedCount > 0) {
				i--;
			}
		}
	}

	/**
	 * Tries to extract a habitat of a spider from the conjuncts based on the
	 * given formula. This method works in the following way: <ul> <li>First it
	 * checks whether the given formula satisfies the <span
	 * style="font-weight:bold">habitat definition condition</span>, which means
	 * that it contains only conjunctively and disjunctively connected (negated
	 * or non-negated) unary relations which mention a unique spider.</li>
	 * <li>Then it extracts the name of the spider that the relations
	 * mention.</li> <li>Afterwards, it finds all other conjuncts that satisfy
	 * the <span style="font-style:italic;">habitat definition condition</span>
	 * and also mention this particular spider.</li> <li>Having done these
	 * steps, the method now has all the conjuncts that specify a spider's
	 * habitat (the full specification of its habitat).</li> <li>TODO: What
	 * happens next?</li> </ul> <p>This method will fail (throw an {@link ConversionException})
	 * if any of the following happens: <ul> <li>The conjunct mentions more than
	 * one spider, or if a non-spider is mentioned in it.</li> <li>The conjunct
	 * contains a non-unary relation.</li> </ul></p>
	 *
	 * @param formulaIdx the index (in {@code conjuncts}) of the formula on
	 * which to base the extraction of the habitat.
	 * @param conjuncts the set of conjuncts from which to extract the habitat.
	 * @param habitats the collection of habitats to which this extracted
	 * habitat will be added.
	 * @param contoursArr a naturally sorted array of all contour names that
	 * should appear in the unitary spider diagram for which this habitat is
	 * being extracted.
	 * @param spidersArr a naturally sorted array of all spider names in the
	 * unitary spider diagram for which this habitat is being extracted.
	 * @return the number of conjuncts that were removed from the list of
	 * conjuncts if the habitat has been successfully extracted, otherwise zero
	 * is returned (which only indicates that this formula does not talk about
	 * habitats).
	 */
	private static int extractHabitat(int formulaIdx, ArrayList<OPFormula> conjuncts, TreeMap<String, Region> habitats, String[] contoursArr, String[] spidersArr) throws ConversionException {
		OPFormula formula = conjuncts.get(formulaIdx);
		// Check that all atoms in this formula are unary predicates with
		// the same spider.
		int spIdx = getSpiderFromPredicates(formula, spidersArr, -1);
		if (spIdx >= 0) {
			// We've got the name of the spider, now extract all other conjuncts
			// that mention only it (also, remove them all from the conjuncts list).
			ArrayList<OPFormula> allConjuncts = new ArrayList<OPFormula>();
			allConjuncts.add(formula);
			conjuncts.remove(formulaIdx);
			for (int i = formulaIdx; i < conjuncts.size(); i++) {
				int spIdx2 = getSpiderFromPredicates(conjuncts.get(i), spidersArr, spIdx);
				if (spIdx2 == spIdx) {
					// Good this conjunct also talks about a habitat of this spider.
					allConjuncts.add(conjuncts.get(i));
					conjuncts.remove(i--);
				} else if (spIdx2 == UNKNOWN_TERM_MENTIONED || spIdx2 == MORE_THAN_ONE_SPIDER_MENTIONED) {
					// This conjunct does not talk about this spider or spider
					// habitats exclusively, ignore it.
				} else {
					throw new ConversionException(speedith.openproof.i18n.Translations.i18n("FOL2SD_UNKNOWN_HABITAT_DEFINITION", conjuncts.get(i).toString()));
				}
			}

			// We now have all the conjuncts that talk about the habitat of the
			// given spider.
			// We currently support these cases:
			//		-	there is only one conjunct:
			//			-	then this conjunct must be a disjunction of fully
			//				specified zones (e.g.: 'A(s) & B(s) | ~A(s) & B(s)').
			//			-	otherwise a conversion exception is thrown.
			//		-	there is more than one conjunct:
			//			-	then these conjuncts must form a full zone
			//				specification (e.g.: 'A(s)' and '~B(s)', if there
			//				are only two contours 'A' and 'B').
			//			-	otherwise a conversion exception is thrown.
			if (allConjuncts.size() > 1) {
				Zone z = extractZone(allConjuncts, contoursArr);
				habitats.put(spidersArr[spIdx], new Region(z));
			} else {
				TreeSet<Zone> zones = new TreeSet<Zone>();
				for (OPFormula zoneSpecification : extractDisjuncts(allConjuncts.get(0))) {
					zones.add(extractZone(extractConjuncts(zoneSpecification), contoursArr));
				}
				habitats.put(spidersArr[spIdx], new Region(zones));
			}

			return allConjuncts.size();
		} else if (spIdx == UNKNOWN_TERM_MENTIONED) {
			// This formula may not be a habitat definition. Ignore it
		} else {
			throw new ConversionException(speedith.openproof.i18n.Translations.i18n("FOL2SD_UNKNOWN_HABITAT_DEFINITION", formula.toString()));
		}
		return 0;
	}

	/**
	 * This method returns the index of the spider diagram if every predicate in
	 * the given formula mentions only it.
	 *
	 * @return <ul> <li>{@link FOLToSpiders#MORE_THAN_ONE_SPIDER_MENTIONED} is
	 * returned if there were at least two different spiders mentioned.</li> <li>{@link FOLToSpiders#NON_SPIDER_MENTIONED}
	 * is returned if an unknown spider has been mentioned (a spider not in the
	 * given list of spiders).</li> <li>{@link FOLToSpiders#NON_UNARY_PREDICATE_MENTIONED}
	 * is returned if a non-unary predicate has been mentioned in the given
	 * formula, or if the predicate uses something else other than the spider in
	 * its arguments.</li><li>{@link FOLToSpiders#UNKNOWN_TERM_MENTIONED} is
	 * returned if a term appears that is not a negated atom connected
	 * disjunctively or conjunctively.</li></ul>
	 */
	private static int getSpiderFromPredicates(OPFormula formula, String[] spidersArr, int expectedSpider) {
		if (formula instanceof OPAtom) {
			OPAtom atom = (OPAtom) formula;
			OPTermList arguments = atom.getArguments();
			if (arguments != null
					&& arguments.count() == 1
					&& arguments.termAt(0) instanceof OPVariable) {
				int spIdx = Arrays.binarySearch(spidersArr, ((OPVariable) arguments.termAt(0)).toString());
				if (spIdx < 0) {
					return NON_SPIDER_MENTIONED;
				} else if (expectedSpider < 0) {
					return spIdx;
				} else {
					return expectedSpider == spIdx ? expectedSpider : MORE_THAN_ONE_SPIDER_MENTIONED;
				}
			} else {
				return NON_UNARY_PREDICATE_MENTIONED;
			}
		} else if (formula instanceof OPDisjunction || formula instanceof OPConjunction) {
			OPFormulaList juncts = ((NAryFormula) formula).getJuncts();
			for (int i = 0; i < juncts.count(); i++) {
				expectedSpider = getSpiderFromPredicates(juncts.formulaAt(i), spidersArr, expectedSpider);
				if (expectedSpider < 0) {
					return expectedSpider;
				}
			}
			return expectedSpider;
		} else if (formula instanceof OPNegation) {
			OPNegation neg = (OPNegation) formula;
			if (neg.getNegated() instanceof OPAtom) {
				return getSpiderFromPredicates(neg.getNegated(), spidersArr, expectedSpider);
			}
		}
		return UNKNOWN_TERM_MENTIONED;
	}

	/**
	 *
	 * @param formulae this parameter contains only formulae that are <span
	 * style="font-weight:bold">only</span> negated or non-negated unary
	 * predicate symbols.
	 * @param contoursArr
	 * @return
	 */
	private static Zone extractZone(ArrayList<OPFormula> formulae, String[] contoursArr) throws ConversionException {
		TreeSet<String> inContours = new TreeSet<String>();
		TreeSet<String> outContours = new TreeSet<String>();
		for (int i = 0; i < formulae.size(); i++) {
			OPFormula formula = formulae.get(i);
			boolean out = false;
			if (formula instanceof OPNegation) {
				formula = ((OPNegation) formula).getNegated();
				out = true;
			}
			if (formula instanceof OPAtom) {
				(out ? outContours : inContours).add(((OPAtom) formula).getPredicateSymbol());
			} else {
				throw new ConversionException(speedith.openproof.i18n.Translations.i18n("FOL2SD_UNKNOWN_ZONE_TERM", formula.toString()));
			}
		}
		// Check that the zone is fully specified:
		if (!Sets.naturallyDisjoint(inContours, outContours)) {
			throw new ConversionException(speedith.openproof.i18n.Translations.i18n("FOL2SD_CONFLICTING_ZONE", Sets.toString(formulae)));
		} else if (inContours.size() + outContours.size() != contoursArr.length) {
			throw new ConversionException(speedith.openproof.i18n.Translations.i18n("FOL2SD_UNDERSPECIFIED_ZONE", Sets.toString(formulae)));
		}
		// NOTE: We could create a set of zones based on partial zone definitions.
		return new Zone(inContours, outContours);
	}
	// </editor-fold>
}
