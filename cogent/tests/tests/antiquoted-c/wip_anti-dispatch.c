/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

int bar ($ty:((A -> A, A)) x)
{
  int ret;
  ret = (($spec:(A -> A))x.p1) (x.p2);
  return ret;
}
