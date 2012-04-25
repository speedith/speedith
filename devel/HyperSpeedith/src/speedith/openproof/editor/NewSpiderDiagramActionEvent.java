package speedith.openproof.editor;

import java.awt.Container;
import java.awt.GridLayout;
import java.awt.Rectangle;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JButton;
import javax.swing.JFrame;

import openproof.zen.EditorFrame;
import openproof.zen.proofeditor.NewDiagramActionEvent;
import openproof.zen.proofeditor.OPEStepInfo;
import openproof.zen.proofeditor.SimpleStepFace;
import speedith.openproof.driver.SpiderDriver;

public class NewSpiderDiagramActionEvent extends NewDiagramActionEvent {
//    public static final String SD_EXAMPLE_1 = "BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD {spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\"], [])]), (\"s'\", [([\"B\"], [])])], sh_zones = []}, operator = \"op -->\" }";
//    public static final String SD_EXAMPLE_2 = "UnarySD {operator = \"op not\", arg1 = BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD {spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\"], [])]), (\"s'\", [([\"B\"], [])])], sh_zones = []}, operator = \"op -->\" }}";
//    public static final String SD_EXAMPLE_3 = "UnarySD {operator = \"op not\", arg1 = BinarySD {operator = \"op &\", arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = NullSD {} }}";
//    public static final String SD_EXAMPLE_4 = "NullSD {}";
//    public static final String SD_EXAMPLE_5 = "PrimarySD { spiders = [], sh_zones = [], habitats = []}";
//    public static final String SD_EXAMPLE_6 = "UnarySD {operator = \"op not\", arg1 = NullSD {}}";
//    public static final String SD_EXAMPLE_7 = "BinarySD {operator = \"op &\", arg1 = NullSD {}, arg2 = NullSD {}}";
//    public static final String SD_EXAMPLE_8 = "BinarySD {operator = \"op -->\", arg1 = NullSD {}, arg2 = NullSD {}}";
//    public static final String SD_EXAMPLE_9 = "BinarySD {arg1 = NullSD {}, arg2 = PrimarySD {spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\"], [])]), (\"s'\", [([\"B\"], [])])], sh_zones = []}, operator = \"op -->\" }";
//    public static final String SD_EXAMPLE_10 = "BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = NullSD {}, operator = \"op -->\" }";
//    public static final String SD_EXAMPLE_11 = "BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s'\", [([\"A\", \"B\"], [])]), (\"s\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, operator = \"op -->\" }";
//    public static final String SD_EXAMPLE_12 = "BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s'\", [([\"A\", \"B\"], [])]), (\"s\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, operator = \"op <-->\" }";
    public static final String SD_EXAMPLE_13 = "BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s'\", [([\"A\", \"B\"], [])]), (\"s\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, operator = \"op &\" }";
    public static final String SD_EXAMPLE_14 = "BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s'\", [([\"A\", \"B\"], [])]), (\"s\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, operator = \"op |\" }";
    public static final String SD_EXAMPLE_15 = "BinarySD {arg1 = PrimarySD { spiders = [\"s\", \"s'\"], sh_zones = [([\"A\", \"B\"],[])], habitats = [(\"s\", [([\"A\", \"B\"], [])]), (\"s'\", [([\"A\"], [\"B\"]), ([\"B\"], [\"A\"])])]}, arg2 = PrimarySD {spiders = [\"s\", \"s'\"], habitats = [(\"s\", [([\"A\"], [\"B\"])]), (\"s'\", [([\"B\"], [\"A\"])])], sh_zones = []}, operator = \"op -->\" }";
    public static final String SD_EXAMPLE_16 = "PrimarySD { spiders = [\"s'\"], sh_zones = [([\"A\", \"B\"],[\"C\", \"D\"])], habitats = [(\"s'\", [([\"A\"], [\"C\", \"D\", \"B\"]), ([\"A\", \"D\"], [\"C\", \"B\"])])]}";
    public static final String SD_EXAMPLE_17 = "PrimarySD { spiders = [\"s1\", \"s2\"], sh_zones = [([\"A\", \"B\"], [])], habitats = [(\"s1\", [([\"A\"], [\"B\"])]), (\"s2\", [([\"B\"], [\"A\"])])], present_zones = [([\"A\", \"B\"], [])]}";
    public static final String SD_EXAMPLE_18 = "PrimarySD { spiders = [\"s1\", \"s2\", \"s3\", \"s4\"], sh_zones = [([\"A\", \"B\"], [])], habitats = [(\"s1\", [([\"A\"], [\"B\"])]), (\"s2\", [([\"B\"], [\"A\"])]), (\"s3\", [([\"B\"], [\"A\"])]), (\"s4\", [([\"B\"], [\"A\"])])], present_zones = [([\"A\", \"B\"], [])]}";
	
	public NewSpiderDiagramActionEvent(Object source, int id, String command) {
		super(source, id, command);
	}

	@Override
	public void execute(Container ppv, SimpleStepFace focusStep, EditorFrame editor) {
		String ss = editor.getExternalRepName(SpiderDriver.REPRESENTATION_NAME);
		
//		JFrame f = new JFrame("Spider Examples");
//		
//		f.getContentPane().setLayout(new GridLayout(3, 3));
//		
//		String selected = "";
//		
//		JButton b = new JButton("13");
//		b.addActionListener(new ActionListener() {
//			public void actionPerformed(ActionEvent e) {
//				selected = SD_EXAMPLE_13;
//			}
//		});
//		
//		JButton b = new JButton("13");
//		b.addActionListener(new ActionListener() {
//			public void actionPerformed(ActionEvent e) {
//				selected = SD_EXAMPLE_13;
//			}
//		});
//		
//		JButton b = new JButton("13");
//		b.addActionListener(new ActionListener() {
//			public void actionPerformed(ActionEvent e) {
//				selected = SD_EXAMPLE_13;
//			}
//		});
//		
//		JButton b = new JButton("13");
//		b.addActionListener(new ActionListener() {
//			public void actionPerformed(ActionEvent e) {
//				selected = SD_EXAMPLE_13;
//			}
//		});
//		JButton b = new JButton("13");
//		b.addActionListener(new ActionListener() {
//			public void actionPerformed(ActionEvent e) {
//				selected = SD_EXAMPLE_13;
//			}
//		});
//		JButton b = new JButton("13");
//		b.addActionListener(new ActionListener() {
//			public void actionPerformed(ActionEvent e) {
//				selected = SD_EXAMPLE_13;
//			}
//		});
		
		if (ss != null) {
			OPEStepInfo opeStepInfo = focusStep.createNewStepInfo(SpiderDriver.REPRESENTATION_NAME, null);
			if (null == opeStepInfo) return;
			
			SpiderInternalEditor stepEdit = (SpiderInternalEditor) opeStepInfo.getOPEEditor();
			
			SpiderExternalEditor sitEdit = (SpiderExternalEditor) stepEdit.getRepEditor();
			JFrame f = sitEdit.showFrame();

			Rectangle r = mainFrameBounds(ppv);
			f.setLocation(r.x+r.width, r.y);
			f.setSize(r.width, r.width-200); // hack!  Make it as wide as the proof window, and a pleasing height.

			sitEdit.setVisible(true);

			focusStep.attachRepresentation(opeStepInfo);
		} else {
			throw new RuntimeException("Unable to find representation for internal name " + ss);
		}
	}
}
