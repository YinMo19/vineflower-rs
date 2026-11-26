// SPDX-License-Identifier: Apache-2.0

package kotlin;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

@Retention(RetentionPolicy.RUNTIME)
@interface Metadata {
  int k();
  String[] d1();
  String[] d2();
  int xs() default 0;
}

// The second function's name index lies outside the JVM string table.
@Metadata(k = 2, d1 = "\0\004\012\002\010\002\032\006\020\0\032\002\060\001\032\006\020\002\032\002\060\001",
  d2 = {"first", "kotlin/Unit"})
class KotlinMetadataBadMemberSubject {
  public static void first() {}
}

// An invalid annotation element type for the multifile facade name.
@Metadata(k = 5, d1 = "\0\004\012\002\010\002\032\006\020\0\032\002\060\001",
  d2 = {"first", "kotlin/Unit"}, xs = 1)
class KotlinMetadataBadFacadeSubject {
  public static void first() {}
}
