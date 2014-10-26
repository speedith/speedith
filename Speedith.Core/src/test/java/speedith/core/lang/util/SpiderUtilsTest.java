package speedith.core.lang.util;

import org.junit.Test;

import java.util.Collections;
import java.util.TreeSet;

import static java.util.Arrays.asList;
import static org.junit.Assert.assertEquals;

public class SpiderUtilsTest {

  @Test
  public void freshSpiderName_MUST_return_s_WHEN_given_no_spiders() {
    assertEquals("s", SpiderUtils.freshSpiderName(Collections.<String>emptySet()));
  }

  @Test
  public void freshSpiderName_MUST_return_s1_WHEN_given_a_spider_s() {
    assertEquals("s1", SpiderUtils.freshSpiderName(new TreeSet<>(asList("s"))));
  }

  @Test
  public void freshSpiderName_MUST_return_s2_WHEN_given_spiders_s_and_s1() {
    assertEquals("s2", SpiderUtils.freshSpiderName(new TreeSet<>(asList("s", "s1"))));
  }

  @Test
  public void freshSpiderName_MUST_return_s3_WHEN_given_spiders_s1_and_s2() {
    assertEquals("s3", SpiderUtils.freshSpiderName(new TreeSet<>(asList("s1", "s2"))));
  }

  @Test
  public void freshSpiderName_MUST_return_s3a_WHEN_given_spiders_s1a_and_s2a() {
    assertEquals("s3a", SpiderUtils.freshSpiderName(new TreeSet<>(asList("s1a", "s2a"))));
  }

}
