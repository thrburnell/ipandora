import { reduxForm, getValues } from 'redux-form'
import EqualityLine from '../../components/InductiveCase/EqualityLine'
import { closeInductiveCaseProofStep, makeInductiveCaseEquality } from '../../actions'

const mapDispatchToProps = (dispatch) => (
  {
    onCloseClick: () => dispatch(closeInductiveCaseProofStep())
  }
)

const submit = (values, dispatch) => {
  return new Promise((resolve, reject) => {

    if (!values.formula) {
      reject({ formula: "Undefined" })
    } else if (!values.justification) {
      reject ({ justification: "Undefined" })
    } else {
      dispatch(makeInductiveCaseEquality(values.formula, values.justification))
        .then(() => resolve())
        .catch(() => reject({ formula: "Invalid step", justification: "Invalid step" }))
    }
  })
}

export default reduxForm({
  form: "addInductiveCaseProofLine",
  fields: ["formula", "justification"],
  onSubmit: submit
}, null, mapDispatchToProps)(EqualityLine)

