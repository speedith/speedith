package speedith;

import org.apache.commons.cli.*;
import speedith.analyser.ProofAnalyserVisitor;
import speedith.cli.AnalyserOptions;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.*;
import java.util.EnumSet;

/**
 * Command line tool to analyse all proofs within a given directory.
 *
 * @author Sven Linker [s.linker@brighton.ac.uk]
 */
public class Analyser {

    public static void main(String[] args) {
        AnalyserOptions options = new AnalyserOptions();
        CommandLineParser parser = new BasicParser();
        HelpFormatter help = new HelpFormatter();
        ProofAnalyserVisitor visitor = new ProofAnalyserVisitor();
        boolean recursive ;

        try {
            CommandLine line = parser.parse(options, args);
            recursive = line.hasOption(AnalyserOptions.RECURSIVE_SHORT);
            if (!line.hasOption(AnalyserOptions.INPUT_SHORT) || !line.hasOption(AnalyserOptions.OUTPUT_SHORT)) {
                help.printHelp("proof-analyser", options);
                return ;
            }
            Path input = FileSystems.getDefault().getPath(line.getOptionValue(AnalyserOptions.INPUT_SHORT));
            int depth = recursive ? Integer.MAX_VALUE : 1;
            Files.walkFileTree(input, EnumSet.of(FileVisitOption.FOLLOW_LINKS), depth, visitor);
            File output = new File(line.getOptionValue(AnalyserOptions.OUTPUT_SHORT));
            FileWriter writer = new FileWriter(output);
            writer.write(visitor.getResult());
            writer.close();
        } catch (ParseException e) {
            help.printHelp("proof-analyser [-R] <-i input dir> <-o output file>", options);

        } catch (NoSuchFileException e) {
            System.out.println("No file with this name exists: " + e.getFile());
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
