package speedith.openproof.driver;

import openproof.zen.archive.OPRepInfo;

/**
 * This class is BS
 */
public class SpiderDriverOPRepInfo extends OPRepInfo {
	/**
	 * The name of the class implementing the rule driver.
	 */
	protected static final String			spiderRuleDriverName = "openproof.text.driver.TextRuleDriver";

	/**
	 * The name of the class implementing the goal driver.
	 */
	protected static final String			spiderGoalDriverName = "";

	/**
	 * The class names that we may need to save?
	 */
	protected static String[]				spiderClassNames = {"openproof.text.driver.TextDriver",
																spiderRuleDriverName,
																spiderGoalDriverName};

	/**
	 * The internal names for textClassNames, in 1-1 correspondence.
	 */
	protected static String[]				spiderIntNames = {"",
															"ruledrvr",
															"goaldrvr"};


	public SpiderDriverOPRepInfo() {
		super(SpiderDriver.REPRESENTATION_NAME, spiderClassNames, spiderIntNames);
	}
}
