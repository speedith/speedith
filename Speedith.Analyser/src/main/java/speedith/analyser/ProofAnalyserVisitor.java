package speedith.analyser;

import speedith.core.reasoning.Proof;
import speedith.core.reasoning.ProofAnalyser;

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
                    int length = ProofAnalyser.length(inputProof);
                    int maxClutter = ProofAnalyser.maximumClutter(inputProof);
                    double avgClutter = ProofAnalyser.averageClutter(inputProof);
                    int velo = ProofAnalyser.maximalClutterVelocity(inputProof);
                    int complexR = ProofAnalyser.complexRuleCount(inputProof);
                    double avgComplex = ProofAnalyser.averageNumberOfComplexRules(inputProof);
                    int interactions = ProofAnalyser.numberOfInteractions(inputProof);
                    double avgInteractions = ProofAnalyser.averageInteractions(inputProof);

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

            }  catch (ClassNotFoundException e) {
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
