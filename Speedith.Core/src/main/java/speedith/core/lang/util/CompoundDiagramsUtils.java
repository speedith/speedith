package speedith.core.lang.util;

import speedith.core.lang.CompoundSpiderDiagram;
import speedith.core.lang.Operator;
import speedith.core.lang.PrimarySpiderDiagram;

public class CompoundDiagramsUtils {
  public static boolean isConjunctionOfPrimaryDiagrams(CompoundSpiderDiagram csd) {return Operator.Conjunction.equals(csd.getOperator()) && csd.getOperand(0) instanceof PrimarySpiderDiagram && csd.getOperand(1) instanceof PrimarySpiderDiagram;}
}
