package speedith.ui.tactics;

import scala.*;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.tactical.TacticApplicationException;
import speedith.core.reasoning.tactical.euler.BasicTactics;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

/**
 * Regular (not accelerated) proof tactics shown in the tactics menu.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public enum TacticMenuItemRegular implements TacticMenuItem {

    Vennify("Introduce all missing zones", "vennify"),
    DeVennify("Remove all shaded zones", "deVennify"),
    UnifyContours("Unify contours in premises", "unifyContourSets"),
    EraseContours("Erase all contours in premises",  "eraseAllContours"),
    CombineAll("Combine as much as possible","combineAll"),
    MatchConc("Match the premises with the conclusion", "matchConclusion"),
    VennStyle("Venn-Style reasoning", "vennStyle"),
    CopyContours("Copy contours as much as possible", "copyTopologicalInformation"),
    CopyShadings("Copy as much shading as possible", "copyShadings")
    ;


    private String name;

    private Method callee;

    /**
     * Creates a new TacticMenuItemRegular. The method that will be called must return
     * a function of the type {@link String} => {@link Proof} => {@link Option}<{@link Proof}>
     *
     * @param name The text that will be displayed in the menu
     * @param methodName The name of the method within {@link BasicTactics}.
     */
    TacticMenuItemRegular(String name, String methodName) {
        this.name = name;
        try {
            this.callee = BasicTactics.class.getDeclaredMethod(methodName);
        } catch (NoSuchMethodException e) {
            e.printStackTrace();
        }
    }

    /**
     * Applies the method of this TacticMenuItemRegular to the given proof.
     * @param proof The proof to which the tactic will be applied to
     * @return the result of applying the tactic to the proof
     * @throws TacticApplicationException If the tactic could not be applied
     */
    @Override
    public Proof apply(Proof proof) throws TacticApplicationException {
        Option<Proof> result = null;
        try {
            Function1<String, Function1<Proof, Option<Proof>>> function = (Function1<String, Function1<Proof,Option<Proof>>>) callee.invoke(BasicTactics.class);
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
            throw new TacticApplicationException("InferenceTactic could not be applied");
        }
        return result.get();
    }

    /**
     *
     * @return the name of this menu item
     */
    @Override
    public String getName() {
        return name;
    }
}
