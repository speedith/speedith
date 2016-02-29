package speedith.ui.tactics;

import scala.*;
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
public enum TacticMenuItem  { //implements Comparable<TacticMenuItem> {

    Vennify("Introduce all missing zones", "vennify"),
    DeVennify("Remove all shaded zones", "deVennify"),
    UnifyContours("Unify contours in premises", "unifyContourSets"),
    EraseContours("Erase all contours in premises",  "eraseAllContours"),
    CombineAll("Combine as much as possible","combineAll"),
    MatchConc("Match the premises with the conclusion", "matchConclusion"),
    VennStyle("Venn-Style reasoning", "vennStyle"),
    CopyContours("Copy contours as much as possible", "copyTopologicalInformation"),
    CopyShadings("Copy as much shading as possible", "copyShadings");


    private String name;

    private Method callee;


    TacticMenuItem(String name, String methodName) {
        this.name = name;
        try {
            this.callee = SimpleTacticals.class.getDeclaredMethod(methodName);
        } catch (NoSuchMethodException e) {
            e.printStackTrace();
        }
    }

    public Proof apply(Proof proof) throws TacticApplicationException {
        Some<Proof> result = null;
        try {
            Function1<Proof, Option<Proof>> function = (Function1<Proof, Option<Proof>>) callee.invoke(SimpleTacticals.class);
            result = (Some<Proof>) function.apply(proof);
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