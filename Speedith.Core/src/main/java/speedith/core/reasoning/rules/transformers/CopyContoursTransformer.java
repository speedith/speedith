package speedith.core.reasoning.rules.transformers;

import speedith.core.lang.CompoundSpiderDiagram;
import speedith.core.lang.IdTransformer;
import speedith.core.lang.SpiderDiagram;

import java.util.ArrayList;

public class CopyContoursTransformer extends IdTransformer {

    public CopyContoursTransformer() {
    }

    @Override
    public SpiderDiagram transform(CompoundSpiderDiagram csd, int diagramIndex, ArrayList<CompoundSpiderDiagram> parents, ArrayList<Integer> childIndices) {
        throw new UnsupportedOperationException();
    }
}
