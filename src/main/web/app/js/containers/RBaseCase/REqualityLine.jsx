import { reduxForm, getValues } from 'redux-form'
import EqualityLine from '../../components/BaseCase/EqualityLine'
import { closeBaseCaseProofStep, makeBaseCaseEquality } from '../../actions'

const mapDispatchToProps = (dispatch) => (
  {
    onCloseClick: () => dispatch(closeBaseCaseProofStep())
  }
)

const submit = (values, dispatch) => {
  return new Promise((resolve, reject) => {

    if (!values.formula) {
      reject({ formula: "Undefined" })
    } else if (!values.justification) {
      reject ({ justification: "Undefined" })
    } else {
      dispatch(makeBaseCaseEquality(values.formula, values.justification))
        .then(() => resolve())
        .catch(() => reject({ formula: "Invalid step", justification: "Invalid step" }))
    }
  })
}

export default reduxForm({
  form: "addBaseCaseProofLine",
  fields: ["formula", "justification"],
  onSubmit: submit
}, null, mapDispatchToProps)(EqualityLine)

