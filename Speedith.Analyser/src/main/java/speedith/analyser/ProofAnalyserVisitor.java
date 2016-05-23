package speedith.analyser;

import speedith.core.reasoning.Proof;
import speedith.core.reasoning.ProofAnalyser;
import speedith.core.reasoning.tactical.TacticApplicationException;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.nio.file.*;
import java.nio.file.attribute.BasicFileAttributes;

/**
 * TODO: Description
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class ProofAnalyserVisitor extends SimpleFileVisitor<Path> {

    private StringBuilder result ;
    private PathMatcher matcher;

    public ProofAnalyserVisitor() {
        result = new StringBuilder();
        result.append("Name, ")
                .append("Length, ")
                .append("Maximal Clutter, ")
                .append("Average Clutter, ")
                .append("Number of complex Rules, ")
                .append("Average number of complex rules, ")
                .append("Interactions, ")
                .append("Average number of Interactions, ")
                .append("Maximal clutter velocity\n");
        matcher = FileSystems.getDefault().getPathMatcher("glob:**.prf");
    }

    @Override
    public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {

        if (attrs.isRegularFile() && matcher.matches(file)) {
            // load and analyse proof

            Proof inputProof;
            try (
                    FileInputStream inputStream = new FileInputStream(file.toFile());
                    ObjectInputStream objectInputStream = new ObjectInputStream(inputStream)) {
                inputProof = (Proof) objectInputStream.readObject();
                if (inputProof != null) {
                    Proof flattened = inputProof.createFlattenedProof();
                    int length = ProofAnalyser.length(flattened);
                    int maxClutter = ProofAnalyser.maximumClutter(flattened);
                    double avgClutter = ProofAnalyser.averageClutter(flattened);
                    int velo = ProofAnalyser.maximalClutterVelocity(flattened);
                    int complexR = ProofAnalyser.complexRuleCount(flattened);
                    double avgComplex = ProofAnalyser.averageNumberOfComplexRules(flattened);
                    int interactions = ProofAnalyser.numberOfInteractions(flattened);
                    double avgInteractions = ProofAnalyser.averageInteractions(flattened);

                    result.append(file.getFileName()).append(", ")
                            .append(length).append(", ")
                            .append(maxClutter).append(", ")
                            .append(String.format("%.2f", avgClutter)).append(", ")
                            .append(complexR).append(", ")
                            .append(String.format("%.2f", avgComplex)).append(", ")
                            .append(interactions).append(", ")
                            .append(String.format("%.2f", avgInteractions)).append(", ")
                            .append(velo).append("\n");

                }

            }  catch (ClassNotFoundException|TacticApplicationException e) {
                e.printStackTrace();
            }
        }

    return FileVisitResult.CONTINUE;
    }

    @Override
    public FileVisitResult postVisitDirectory(Path dir, IOException exc) throws IOException {
        return FileVisitResult.CONTINUE;
    }

    public String getResult() {
        return result.toString();
    }
}
