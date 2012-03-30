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

/**
 * Converts an Openproof {@link OPFormula FOL formula} into a {@link SpiderDiagram spider diagram}.
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class FOLToSpiders {

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
		throw new ConversionException(speedith.openproof.i18n.Translations.i18n("FOL2SD_NOT_IMPLEMENTED_YET", binaryFormula.toString()));
	}
	
	private static CompoundSpiderDiagram unary2csd(UnaryFormula unaryFormula, Operator operator) throws ConversionException {
		throw new ConversionException(speedith.openproof.i18n.Translations.i18n("FOL2SD_NOT_IMPLEMENTED_YET", unaryFormula.toString()));
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

		// TODO: Extract habitats...

		// SHADED ZONES STUFF:
		// TODO: Implement parsing for shaded zones.

		return SpiderDiagrams.createPrimarySDNoCopy(spiders, null, null, null);
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
	
	private static void extractHabitats(ArrayList<OPFormula> conjuncts, TreeMap<String, Region> habitats, String[] contoursArr, String[] spidersArr) {
		for (int i = 0; i < conjuncts.size(); i++) {
			OPFormula conjunct = conjuncts.get(i);
			String extracted = extractFullHabitat(conjunct, habitats, contoursArr, spidersArr);
		}
	}

	/**
	 * A full habitat is one that contains disjunctively connected zones. An
	 * example of a full habitat is: 'A(t) & B(t) | ~A(t) & B(t) | A(t) &
	 * ~B(t)'.
	 *
	 * @param conjunct
	 * @param habitats
	 * @param contoursArr
	 * @param spidersArr
	 * @return the spider for which the habitat has been extracted.
	 */
	private static String extractFullHabitat(OPFormula conjunct, TreeMap<String, Region> habitats, String[] contoursArr, String[] spidersArr) {
		if (conjunct instanceof OPDisjunction) {
			final ArrayList<OPFormula> disjuncts = new ArrayList<OPFormula>();
			extractDisjuncts(conjunct, disjuncts);
			ArrayList<Zone> zones = new ArrayList<Zone>();
			for (OPFormula disjunct : disjuncts) {
				// TODO: Extract Zone...
//				String spider = extractZone(disjunct, contour);
			}
		}
		return null;
	}
	// </editor-fold>
}
