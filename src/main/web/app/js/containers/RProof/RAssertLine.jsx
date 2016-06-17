import { reduxForm, getValues } from 'redux-form'
import AssertLine from '../../components/Proof/AssertLine'
import { closeProofStep, makeAssertion } from '../../actions'

const mapDispatchToProps = (dispatch) => (
  {
    onCloseClick: () => dispatch(closeProofStep())
  }
)

const submit = (values, dispatch) => {
  return new Promise((resolve, reject) => {
    if (!values.formula) {
      reject({ formula: "Undefined" })
    } else if (!values.justification) {
      reject ({ justification: "Undefined" })
    } else {
      dispatch(makeAssertion(values.formula, values.justification))
        .then(() => resolve())
        .catch(() => reject({ formula: "Invalid step", justification: "Invalid step" }))
    }
  })
}

export default reduxForm({
  form: "addProofLine",
  fields: ["formula", "justification"],
  onSubmit: submit
}, null, mapDispatchToProps)(AssertLine)

