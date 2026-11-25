// SPDX-License-Identifier: Apache-2.0

import java.util.List;
import java.util.ListIterator;

public class TestListIteratorHierarchy {
  public void print(List<String> values) {
    ListIterator<String> iterator = values.listIterator();
    while (iterator.hasNext()) {
      String value = iterator.next();
      System.out.println(value);
    }
  }
}
