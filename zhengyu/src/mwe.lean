inductive weekday -- inductively define a type
| monday | tuesday | wednesday | thursday | friday | saturday | sunday
namespace weekday
open weekday (renaming rec -> rec)
def next (d: weekday) := rec tuesday wednesday thursday friday saturday sunday monday d
end weekday