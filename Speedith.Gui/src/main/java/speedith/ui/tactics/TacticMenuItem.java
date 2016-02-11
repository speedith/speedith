package speedith.ui.tactics;

import scala.Some;
import speedith.core.reasoning.Proof;
import speedith.core.reasoning.tactical.TacticApplicationException;
import speedith.core.reasoning.tactical.euler.SimpleTacticals;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public enum TacticMenuItem implements Comparable<TacticMenuItem> {

    Vennify("Introduce all missing zones", "vennify"),
    DeVennify("Remove all shaded zones", "deVennify"),
    UnifyContours("Unify contours in premises", "unifyContourSets"),
    EraseContours("Erase all contours in premises",  "eraseAllContours"),
    CombineAll("Combine as much as possible","combineAll"),
    VennStyle("Try a Venn-Style proof", "vennStyle"),
    MatchConc("Match the premises with the conclusion", "matchConclusion"),
    CopyContours("Copy contours as much as possible", "copyTopologicalInformation"),
    CopyShadings("Copy as much shading as possible", "copyShadings");


    private String name;

    private Method callee;


    TacticMenuItem(String name, String methodName) {
        this.name = name;
        try {
            this.callee = SimpleTacticals.class.getDeclaredMethod(methodName, Proof.class);
        } catch (NoSuchMethodException e) {
            e.printStackTrace();
        }
    }

    public Proof apply(Proof proof) throws TacticApplicationException {
        Some<Proof> result = null;
        try {
            result = (Some<Proof>) callee.invoke(SimpleTacticals.class, proof);
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

    public String getName() {
        return name;
    }
}
