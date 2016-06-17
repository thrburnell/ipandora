import { reduxForm } from 'redux-form'
import AssumeLine from '../../components/Proof/AssumeLine'
import { closeProofStep, makeAssumption } from '../../actions'

const mapDispatchToProps = (dispatch) => (
  {
    onCloseClick: () => dispatch(closeProofStep())
  }
)

const submit = (values, dispatch) => {
  return new Promise((resolve, reject) => {

    if (!values.formula) {
      reject({ formula: "Undefined" })
    } else {
      dispatch(makeAssumption(values.formula))
        .then(() => resolve())
        .catch(() => reject({ formula: "Invalid" }))
    }
  })
}

export default reduxForm({
  form: "addAssumeLine",
  fields: ["formula"],
  onSubmit: submit
}, null, mapDispatchToProps)(AssumeLine)

