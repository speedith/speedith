package speedith.ui.tactics;

import scala.*;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.tactical.TacticApplicationException;
import speedith.core.reasoning.tactical.euler.SimpleTacticals;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

/**
 * Items shown in the tactics menu.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public enum TacticMenuItem  { //implements Comparable<TacticMenuItem> {

    Vennify("Introduce all missing zones", "vennify"),
    DeVennify("Remove all shaded zones", "deVennify"),
    DeVennifyFast("Remove all shaded zones (fast)", "deVennifyFast"),

    UnifyContours("Unify contours in premises", "unifyContourSets"),
    UnifyContoursFast("Unify contours in premises (fast)", "unifyContourSetsFast"),
    EraseContours("Erase all contours in premises",  "eraseAllContours"),
    CombineAll("Combine as much as possible","combineAll"),
    MatchConc("Match the premises with the conclusion", "matchConclusion"),
    MatchConcFast("Match the premises with the conclusion (fast)", "matchConclusionFast"),
    VennStyle("Venn-Style reasoning", "vennStyle"),
    VennStyleFast("Venn-Style reasoning (fast)", "vennStyleFast"),
    CopyContours("Copy contours as much as possible", "copyTopologicalInformation"),
    CopyShadings("Copy as much shading as possible", "copyShadings");


    private String name;

    private Method callee;

    /**
     * Creates a new TacticMenuItem. The method that will be called must return
     * a function of the type {@link String} => {@link Proof} => {@link Option}<{@link Proof}>
     *
     * @param name The text that will be displayed in the menu
     * @param methodName The name of the method within {@link SimpleTacticals}.
     */
    TacticMenuItem(String name, String methodName) {
        this.name = name;
        try {
            this.callee = SimpleTacticals.class.getDeclaredMethod(methodName);
        } catch (NoSuchMethodException e) {
            e.printStackTrace();
        }
    }

    /**
     * Applies the method of this TacticMenuItem to the given proof.
     * @param proof The proof to which the tactic will be applied to
     * @return the result of applying the tactic to the proof
     * @throws TacticApplicationException If the tactic could not be applied
     */
    public Proof apply(Proof proof) throws TacticApplicationException {
        Option<Proof> result = null;
        try {
            Function1<String, Function1<Proof, Option<Proof>>> function = (Function1<String, Function1<Proof,Option<Proof>>>) callee.invoke(SimpleTacticals.class);
            result = function.apply(getName()).apply(proof);
        } catch (IllegalAccessException e) {
            e.printStackTrace();
        } catch (InvocationTargetException e) {
            e.printStackTrace();
            if (e.getCause() instanceof TacticApplicationException) {
                throw (TacticApplicationException) e.getCause();
            }
        }
        if (result == null || result.isEmpty()) {
            throw new TacticApplicationException("Tactic could not be applied");
        }
        return result.get();
    }

    /**
     *
     * @return the name of this menu item
     */
    public String getName() {
        return name;
    }
}
